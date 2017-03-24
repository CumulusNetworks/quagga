/* BGP EVPN
 * Copyright (C) 2016 Cumulus Networks, Inc.
 *
 * This file is part of Quagga.
 *
 * Quagga is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * Quagga is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GN5U General Public License
 * along with Quagga; see the file COPYING.  If not, write to the Free
 * Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 */

#include "command.h"
#include "stream.h"
#include "memory.h"
#include "log.h"
#include "hash.h"
#include "prefix.h"
#include "zclient.h"
#include "vxlan.h"
#include "filter.h"

#include "bgpd/bgpd.h"
#include "bgpd/bgp_table.h"
#include "bgpd/bgp_route.h"
#include "bgpd/bgp_evpn.h"
#include "bgpd/bgp_attr.h"
#include "bgpd/bgp_debug.h"
#include "bgpd/bgp_aspath.h"
#include "bgpd/bgp_community.h"
#include "bgpd/bgp_ecommunity.h"
#include "bgpd/bgp_rd.h"
#include "bgpd/bgp_mplsvpn.h"
#include "bgpd/bgp_zebra.h"
#include "linklist.h"
#include "jhash.h"

/*
 * Definitions and external declarations.
 */
#define EVPN_TYPE_2_ROUTE_PREFIXLEN      192
#define EVPN_TYPE_3_ROUTE_PREFIXLEN      192

extern struct zclient *zclient;

DEFINE_QOBJ_TYPE(bgpevpn)


/*
 * Private functions.
 */

/*
 * Make vni hash key.
 */
static unsigned int
vni_hash_key_make(void *p)
{
  struct bgpevpn *vpn = p;
  return (jhash_1word(vpn->vni, 0));
}

/*
 * Comparison function for vni hash
 */
static int
vni_hash_cmp (const void *p1, const void *p2)
{
  const struct bgpevpn *vpn1 = p1;
  const struct bgpevpn *vpn2 = p2;

  if (!vpn1 && !vpn2)
    return 1;
  if (!vpn1 || !vpn2)
    return 0;
  return(vpn1->vni == vpn2->vni);
}

/*
 * Make import route target hash key.
 */
static unsigned int
import_rt_hash_key_make (void *p)
{
  struct irt_node *irt = p;
  char *pnt = irt->rt.val;
  unsigned int key = 0;
  int c=0;

  key += pnt[c];
  key += pnt[c + 1];
  key += pnt[c + 2];
  key += pnt[c + 3];
  key += pnt[c + 4];
  key += pnt[c + 5];
  key += pnt[c + 6];
  key += pnt[c + 7];

  return (key);
}

/*
 * Comparison function for import rt hash
 */
static int
import_rt_hash_cmp (const void *p1, const void *p2)
{
  const struct irt_node *irt1 = p1;
  const struct irt_node *irt2 = p2;

  if (irt1 == NULL && irt2 == NULL)
    return 1;

  if (irt1 == NULL || irt2 == NULL)
    return 0;

  return(memcmp(irt1->rt.val, irt2->rt.val, ECOMMUNITY_SIZE) == 0);
}

/*
 * Create a new import_rt
 */
static struct irt_node *
import_rt_new (struct bgp *bgp, struct ecommunity_val *rt)
{
  struct irt_node *irt;

  if (!bgp)
    return NULL;

  irt = XCALLOC (MTYPE_BGP_EVPN_IMPORT_RT, sizeof (struct irt_node));
  if (!irt)
    return NULL;

  irt->rt = *rt;
  irt->vnis = list_new ();

  /* Add to hash */
  if (!hash_get(bgp->import_rt_hash, irt, hash_alloc_intern))
    {
      XFREE(MTYPE_BGP_EVPN_IMPORT_RT, irt);
      return NULL;
    }

  return irt;
}

/*
 * Free the import rt node
 */
static void
import_rt_free (struct bgp *bgp, struct irt_node *irt)
{
  hash_release(bgp->import_rt_hash, irt);
  XFREE(MTYPE_BGP_EVPN_IMPORT_RT, irt);
}

/*
 * Function to lookup Import RT node - used to map a RT to set of
 * VNIs importing routes with that RT.
 */
static struct irt_node *
lookup_import_rt (struct bgp *bgp, struct ecommunity_val *rt)
{
  struct irt_node *irt;
  struct irt_node tmp;

  memset(&tmp, 0, sizeof(struct irt_node));
  memcpy(&tmp.rt, rt, ECOMMUNITY_SIZE);
  irt = hash_lookup(bgp->import_rt_hash, &tmp);
  return irt;
}

/*
 * Is specified VNI present on the RT's list of "importing" VNIs?
 */
static int
is_vni_present_in_irt_vnis (struct list *vnis, struct bgpevpn *vpn)
{
  struct listnode *node, *nnode;
  struct bgpevpn *tmp_vpn;

  for (ALL_LIST_ELEMENTS (vnis, node, nnode, tmp_vpn))
    {
      if (tmp_vpn == vpn)
        return 1;
    }

  return 0;
}

/*
 * Mask off global-admin field of specified extended community (RT)
 */
static inline void
mask_ecom_global_admin (struct ecommunity_val *dst,
                        struct ecommunity_val *src)
{
  u_char type;

  type = src->val[0];
  if (type == ECOMMUNITY_ENCODE_AS)
    dst->val[2] = dst->val[3] = 0;
  else if (type == ECOMMUNITY_ENCODE_AS4)
    {
      dst->val[2] = dst->val[3] = 0;
      dst->val[4] = dst->val[5] = 0;
    }
}

/*
 * Map one RT to specified VNI.
 */
static void
map_vni_to_rt (struct bgp *bgp, struct bgpevpn *vpn,
               struct ecommunity_val *eval)
{
  struct irt_node *irt;
  struct ecommunity_val eval_tmp;

  /* If using "automatic" RT, we only care about the local-admin sub-field.
   * This is to facilitate using VNI as the RT for EBGP peering too.
   */
  memcpy (&eval_tmp, eval, ECOMMUNITY_SIZE);
  if (!is_import_rt_configured (vpn))
    mask_ecom_global_admin (&eval_tmp, eval);

  irt = lookup_import_rt (bgp, &eval_tmp);
  if (irt && irt->vnis)
    if (is_vni_present_in_irt_vnis (irt->vnis, vpn))
      /* Already mapped. */
      return;

  if (!irt)
    {
      irt = import_rt_new (bgp, &eval_tmp);
      assert (irt);
    }

  /* Add VNI to the hash list for this RT. */
  listnode_add (irt->vnis, vpn);
}

/*
 * Unmap specified VNI from specified RT. If there are no other
 * VNIs for this RT, then the RT hash is deleted.
 */
static void
unmap_vni_from_rt (struct bgp *bgp, struct bgpevpn *vpn,
                   struct irt_node *irt)
{
  /* Delete VNI from hash list for this RT. */
  listnode_delete (irt->vnis, vpn);
  if (!listnode_head (irt->vnis))
    {
      list_free (irt->vnis);
      import_rt_free (bgp, irt);
    }
}

/*
 * Create RT extended community automatically from passed information:
 * of the form AS:VNI
 */
static void
form_auto_rt (struct bgp *bgp, struct bgpevpn *vpn,
                       struct ecommunity **ecom_list)
{
  u_char rt_type;
  struct in_addr ip = { .s_addr = INADDR_ANY };
  struct ecommunity_val eval;
  struct ecommunity *ecom;

  if (bgp->as > BGP_AS_MAX)
    rt_type = ECOMMUNITY_ENCODE_AS4;
  else
    rt_type = ECOMMUNITY_ENCODE_AS;
  ecommunity_encode (rt_type, ECOMMUNITY_ROUTE_TARGET, 1, bgp->as,
                     ip, vpn->vni, &eval);
  ecom = ecommunity_new ();
  ecommunity_add_val (ecom, &eval);
  *ecom_list = ecom;
}

/*
 * Derive RD and RT for a VNI automatically. Invoked at the time of
 * creation of a VNI.
 */
static void
derive_rd_rt_for_vni (struct bgp *bgp, struct bgpevpn *vpn)
{
  bgp_evpn_derive_auto_rd (bgp, vpn);
  bgp_evpn_derive_auto_rt_import (bgp, vpn);
  bgp_evpn_derive_auto_rt_export (bgp, vpn);
}

/*
 * Free a VNI entry; iterator function called during cleanup.
 */
static void
free_vni_entry (struct hash_backet *backet, struct bgp *bgp)
{
  struct bgpevpn *vpn;

  vpn = (struct bgpevpn *) backet->data;
  bgp_evpn_free(bgp, vpn);
}

/*
 * Add (update) or delete MAC from zebra.
 */
static int
bgp_zebra_send_remote_mac (struct bgp *bgp, struct bgpevpn *vpn,
                           struct prefix_evpn *p, struct in_addr remote_vtep_ip,
                           int add)
{
  struct stream *s;
  char buf1[MACADDR_STRLEN];
  char buf2[PREFIX2STR_BUFFER];

  /* Check socket. */
  if (!zclient || zclient->sock < 0)
    return 0;

  /* Don't try to register if Zebra doesn't know of this instance. */
  if (!IS_BGP_INST_KNOWN_TO_ZEBRA(bgp))
    return 0;

  s = zclient->obuf;
  stream_reset (s);

  zclient_create_header (s, add ? ZEBRA_REMOTE_MACIP_ADD : ZEBRA_REMOTE_MACIP_DEL,
                         bgp->vrf_id);
  stream_putl(s, vpn->vni);
  stream_put (s, &p->prefix.mac.octet, ETHER_ADDR_LEN); /* Mac Addr */
  stream_putl(s, 0); /* IP address length. */
  stream_put_in_addr(s, &remote_vtep_ip);

  stream_putw_at (s, 0, stream_get_endp (s));

  if (bgp_debug_zebra (NULL))
    zlog_debug("Tx %s MAC, VNI %u MAC %s remote VTEP %s",
               add ? "ADD" : "DEL", vpn->vni,
               mac2str (&p->prefix.mac, buf1, sizeof(buf1)),
               inet_ntop(AF_INET, &remote_vtep_ip, buf2, sizeof(buf2)));

  return zclient_send_message(zclient);
}

/*
 * Add (update) or delete remote VTEP from zebra.
 */
static int
bgp_zebra_send_remote_vtep (struct bgp *bgp, struct bgpevpn *vpn,
                            struct prefix_evpn *p, int add)
{
  struct stream *s;
  char buf[PREFIX2STR_BUFFER];
  u_int16_t family;

  /* Check socket. */
  if (!zclient || zclient->sock < 0)
    return 0;

  /* Don't try to register if Zebra doesn't know of this instance. */
  if (!IS_BGP_INST_KNOWN_TO_ZEBRA(bgp))
    return 0;

  s = zclient->obuf;
  stream_reset (s);

  zclient_create_header (s, add ? ZEBRA_REMOTE_VTEP_ADD : ZEBRA_REMOTE_VTEP_DEL,
                         bgp->vrf_id);
  stream_putl(s, vpn->vni);
  stream_putc(s, 0); // flags - unused
  if (IS_EVPN_PREFIX_IPADDR_V4(p))
    {
      family = AF_INET;
      stream_putw(s, family);
      stream_putc(s, IPV4_MAX_BITLEN);
      stream_put_in_addr(s, &p->prefix.ip.v4_addr);
    }
  else if (IS_EVPN_PREFIX_IPADDR_V6(p))
    {
      family = AF_INET6;
      stream_putw(s, AF_INET6);
      stream_putc(s, IPV6_MAX_BITLEN);
      stream_put(s, &p->prefix.ip.v6_addr, IPV6_MAX_BYTELEN);
    }
  else
    {
      zlog_err ("Bad remote IP when trying to %s remote VTEP for VNI %u",
                add ? "ADD" : "DEL", vpn->vni);
      return -1;
    }

  stream_putw_at (s, 0, stream_get_endp (s));

  if (bgp_debug_zebra (NULL))
    zlog_debug("Tx %s Remote VTEP, VNI %u remote VTEP %s",
               add ? "ADD" : "DEL", vpn->vni,
               inet_ntop(family, &p->prefix.ip, buf, sizeof(buf)));

  return zclient_send_message(zclient);
}

/*
 * Build EVPN type-2 prefix (for route node)
 */
static inline void
build_evpn_type2_prefix (struct prefix_evpn *p, struct ethaddr *mac,
                         vni_t vni)
{
  memset (p, 0, sizeof (struct prefix_evpn));
  p->family = AF_ETHERNET;
  p->prefixlen = EVPN_TYPE_2_ROUTE_PREFIXLEN;
  p->prefix.route_type = BGP_EVPN_MAC_IP_ROUTE;
  memcpy(&p->prefix.mac.octet, mac->octet, ETHER_ADDR_LEN);
  p->prefix.ipa_type = IP_ADDR_NONE;
  p->prefix.vni = vni;
}

/*
 * Build EVPN type-3 prefix (for route node)
 */
static inline void
build_evpn_type3_prefix (struct prefix_evpn *p, struct in_addr originator_ip)
{
  memset (p, 0, sizeof (struct prefix_evpn));
  p->family = AF_ETHERNET;
  p->prefixlen = EVPN_TYPE_3_ROUTE_PREFIXLEN;
  p->prefix.route_type = BGP_EVPN_IMET_ROUTE;
  p->prefix.ipa_type = IP_ADDR_V4;
  p->prefix.ip.v4_addr = originator_ip;
}

/*
 * Create or update EVPN route (of type based on prefix) for specified VNI
 * and schedule for processing.
 */
static int
update_evpn_route (struct bgp *bgp, struct bgpevpn *vpn,
                   struct prefix_evpn *p)
{
  struct bgp_node *rn;
  struct attr attr;
  struct bgp_info *ri;
  struct attr *attr_new;
  afi_t afi = AFI_L2VPN;
  safi_t safi = SAFI_EVPN;

  memset (&attr, 0, sizeof (struct attr));

  /* Create route node. EVPN routes have a 2-level tree (RD-level +
   * Prefix-level) similar to L3VPN routes.
   */
  rn = bgp_afi_node_get (bgp->rib[afi][safi], afi, safi,
                         (struct prefix *)p, &vpn->prd);

  /* Build path-attribute for this route. */
  bgp_attr_default_set (&attr, BGP_ORIGIN_IGP);
  attr.nexthop = vpn->originator_ip;
  /* Set up RT extended community. */
  (bgp_attr_extra_get (&attr))->ecommunity = ecommunity_dup (vpn->export_rtl);
  attr.flag |= ATTR_FLAG_BIT (BGP_ATTR_EXT_COMMUNITIES);

  /* Add to hash. */
  attr_new = bgp_attr_intern (&attr);

  /* See if this is an update of an existing route, or a new add. */
  for (ri = rn->info; ri; ri = ri->next)
    if (ri->peer == bgp->peer_self
        && ri->type == ZEBRA_ROUTE_BGP
        && ri->sub_type == BGP_ROUTE_STATIC)
      break;

  /* If route doesn't exist already, create a new one, otherwise act
   * based on whether the attributes of the route have changed or not.
   */
  if (!ri)
    {
      /* Create new route. */
      ri = info_make (ZEBRA_ROUTE_BGP, BGP_ROUTE_STATIC, 0,
                      bgp->peer_self, attr_new, rn);
      SET_FLAG (ri->flags, BGP_INFO_VALID);
      bgp_info_add (rn, ri);
    }
  else
    {
      if (attrhash_cmp (ri->attr, attr_new) &&
          !CHECK_FLAG(ri->flags, BGP_INFO_REMOVED))
        {
          /* Unintern newly created. */
          bgp_attr_unintern (&attr_new);

          /* Unintern temporary. */
          aspath_unintern (&attr.aspath);
          bgp_attr_extra_free (&attr);

          bgp_unlock_node (rn);
          return 0;
        }
      else
        {
          /* The attribute is changed. */
          bgp_info_set_flag (rn, ri, BGP_INFO_ATTR_CHANGED);

          /* Restore route, if needed. */
          if (CHECK_FLAG(ri->flags, BGP_INFO_REMOVED))
            bgp_info_restore(rn, ri);

          /* Unintern existing, set to new. */
          bgp_attr_unintern (&ri->attr);
          ri->attr = attr_new;
          ri->uptime = bgp_clock ();
        }
    }

  bgp_unlock_node (rn);

  /* Schedule for processing. */
  bgp_process (bgp, rn, afi, safi);

  /* Unintern temporary. */
  aspath_unintern (&attr.aspath);
  bgp_attr_extra_free (&attr);

  return 0;
}

/*
 * Delete EVPN route (of type based on prefix) for specified VNI and
 * schedule for processing.
 */
static int
delete_evpn_route (struct bgp *bgp, struct bgpevpn *vpn,
                   struct prefix_evpn *p)
{
  struct bgp_node *rn;
  struct bgp_info *ri;
  afi_t afi = AFI_L2VPN;
  safi_t safi = SAFI_EVPN;

  /* Locate route node. */
  rn = bgp_afi_node_lookup (bgp->rib[afi][safi], afi, safi,
                         (struct prefix *)p, &vpn->prd);

  if (!rn)
    return 0;

  /* Now, find matching route. */
  for (ri = rn->info; ri; ri = ri->next)
    if (ri->peer == bgp->peer_self
        && ri->type == ZEBRA_ROUTE_BGP
        && ri->sub_type == BGP_ROUTE_STATIC)
      break;

  if (ri)
    {
      /* Mark route for delete and schedule for processing. */
      bgp_info_delete (rn, ri);
      bgp_process (bgp, rn, afi, safi);
    }

  /* unlock - for the lookup */
  bgp_unlock_node (rn);
  return 0;
}

/*
 * Update all type-2 (MACIP) local routes for this VNI - these should also
 * be scheduled for advertise to peers.
 */
static int
update_all_type2_routes (struct bgp *bgp, struct bgpevpn *vpn)
{
  afi_t afi;
  safi_t safi;
  struct bgp_node *rdrn, *rn;
  struct bgp_table *table;
  struct bgp_info *ri;
  struct attr attr;
  struct attr *attr_new;

  afi = AFI_L2VPN;
  safi = SAFI_EVPN;
  memset (&attr, 0, sizeof (struct attr));

  /* Build path-attribute - all type-2 routes for this VNI will share the
   * same path attribute.
   */
  bgp_attr_default_set (&attr, BGP_ORIGIN_IGP);
  attr.nexthop = vpn->originator_ip;
  /* Set up RT extended community. */
  (bgp_attr_extra_get (&attr))->ecommunity = ecommunity_dup (vpn->export_rtl);
  attr.flag |= ATTR_FLAG_BIT (BGP_ATTR_EXT_COMMUNITIES);

  /* TODO: We're walking entire table for this VNI, this should be optimized later. */
  /* EVPN routes are a 2-level table, first get the RD table. */
  rdrn = bgp_node_lookup (bgp->rib[afi][safi], (struct prefix *) &vpn->prd);
  if (!rdrn)
    return -1;

  if (rdrn->info == NULL)
    {
      bgp_unlock_node (rdrn);
      return -1;
    }

  table = (struct bgp_table *)rdrn->info;
  for (rn = bgp_table_top (table); rn; rn = bgp_route_next (rn))
    {
      struct prefix_evpn *evp = (struct prefix_evpn *)&rn->p;

      if (evp->prefix.route_type != BGP_EVPN_MAC_IP_ROUTE)
        continue;

      for (ri = rn->info; ri; ri = ri->next)
        if (CHECK_FLAG (ri->flags, BGP_INFO_SELECTED)
            && ri->type == ZEBRA_ROUTE_BGP
            && ri->sub_type == BGP_ROUTE_STATIC)
          break;

      if (ri)
        {
          /* Add/update attribute in hash - for each route. */
          attr_new = bgp_attr_intern (&attr);

          if (attrhash_cmp (ri->attr, attr_new) &&
              !CHECK_FLAG(ri->flags, BGP_INFO_REMOVED))
            {
              /* Unintern newly created. */
              bgp_attr_unintern (&attr_new);
            }
          else
            {
              /* The attribute is changed. */
              bgp_info_set_flag (rn, ri, BGP_INFO_ATTR_CHANGED);

              /* Restore route, if needed. */
              if (CHECK_FLAG(ri->flags, BGP_INFO_REMOVED))
                bgp_info_restore(rn, ri);

              /* Unintern existing, set to new. */
              bgp_attr_unintern (&ri->attr);
              ri->attr = attr_new;
              ri->uptime = bgp_clock ();

              /* Schedule for processing. */
              bgp_process (bgp, rn, afi, safi);
            }
        }
    }

  /* Unintern temporary. */
  aspath_unintern (&attr.aspath);
  bgp_attr_extra_free (&attr);

  /* unlock - for the lookup */
  bgp_unlock_node (rdrn);

  return 0;
}

/*
 * Delete all type-2 (MACIP) local routes for this VNI - these should also
 * be scheduled for withdraw from peers.
 */
static int
delete_all_type2_routes (struct bgp *bgp, struct bgpevpn *vpn)
{
  afi_t afi;
  safi_t safi;
  struct bgp_node *rdrn, *rn;
  struct bgp_table *table;
  struct bgp_info *ri;

  afi = AFI_L2VPN;
  safi = SAFI_EVPN;

  /* TODO: We're walking entire table for this VNI, this should be optimized later. */
  /* EVPN routes are a 2-level table, first get the RD table. */
  rdrn = bgp_node_lookup (bgp->rib[afi][safi], (struct prefix *) &vpn->prd);
  if (!rdrn)
    return -1;

  if (rdrn->info == NULL)
    {
      bgp_unlock_node (rdrn);
      return -1;
    }

  table = (struct bgp_table *)rdrn->info;
  for (rn = bgp_table_top (table); rn; rn = bgp_route_next (rn))
    {
      struct prefix_evpn *evp = (struct prefix_evpn *)&rn->p;

      if (evp->prefix.route_type != BGP_EVPN_MAC_IP_ROUTE)
        continue;

      for (ri = rn->info; ri; ri = ri->next)
        if (CHECK_FLAG (ri->flags, BGP_INFO_SELECTED)
            && ri->type == ZEBRA_ROUTE_BGP
            && ri->sub_type == BGP_ROUTE_STATIC)
          break;

      if (ri)
        {
          /* Mark route for delete and schedule for processing. */
          bgp_info_delete (rn, ri);
          bgp_process (bgp, rn, afi, safi);
        }
    }

  /* unlock - for the lookup */
  bgp_unlock_node (rdrn);

  return 0;
}

/*
 * Update (and advertise) local routes for a VNI. Invoked upon the VNI
 * export RT getting modified.
 */
static int
update_routes_for_vni (struct bgp *bgp, struct bgpevpn *vpn)
{
  int ret;
  struct prefix_evpn p;

  /* Update and advertise the type-3 route (only one) followed by the
   * locally learnt type-2 routes (MACIP) - for this VNI.
   */
  build_evpn_type3_prefix (&p, vpn->originator_ip);
  ret = update_evpn_route (bgp, vpn, &p);
  if (ret)
    return ret;

  return update_all_type2_routes (bgp, vpn);
}

/*
 * Delete (and withdraw) local routes for a VNI. Invoked upon the VNI
 * being deleted or EVPN (advertise-vni) being disabled.
 */
static int
delete_routes_for_vni (struct bgp *bgp, struct bgpevpn *vpn)
{
  int ret;
  struct prefix_evpn p;

  /* Delete and withdraw locally learnt type-2 routes (MACIP)
   * followed by type-3 routes (only one) - for this VNI.
   */
  ret = delete_all_type2_routes (bgp, vpn);
  if (ret)
    return ret;

  build_evpn_type3_prefix (&p, vpn->originator_ip);
  return delete_evpn_route (bgp, vpn, &p);
}

/*
 * Iterator for cleaning up a VNI.
 */
static void
cleanup_vni_on_disable (struct hash_backet *backet, struct bgp *bgp)
{
  struct bgpevpn *vpn = (struct bgpevpn *) backet->data;

  /* Remove EVPN routes and schedule for processing. */
  delete_routes_for_vni (bgp, vpn);

  /* Clear "live" flag and see if hash needs to be freed. */
  UNSET_FLAG (vpn->flags, VNI_FLAG_LIVE);
  if (!is_vni_configured (vpn))
    bgp_evpn_free (bgp, vpn);
}

static void
update_router_id_vni (struct hash_backet *backet, struct bgp *bgp)
{
  struct bgpevpn *vpn;
  struct prefix_evpn p;

  vpn = (struct bgpevpn *) backet->data;

  if (!vpn)
    {
      zlog_warn ("%s: VNI hash entry for VNI not found",
                 __FUNCTION__);
      return;
    }

  bgp_evpn_derive_auto_rd (bgp, vpn);

  /* Create EVPN type-3 route and schedule for processing. */
  build_evpn_type3_prefix (&p, vpn->originator_ip);
  update_evpn_route (bgp, vpn, &p);
}

/*
 * Withdraw the route from peer before updating the router id in evpn cache.
 */
static void
withdraw_router_id_vni (struct hash_backet *backet, struct bgp *bgp)
{
  struct bgpevpn *vpn;
  struct prefix_evpn p;

  vpn = (struct bgpevpn *) backet->data;

  if (!vpn)
    {
      zlog_warn ("%s: VNI hash entry for VNI not found",
                 __FUNCTION__);
      return;
    }

  /* Remove EVPN type-3 route and schedule for processing. */
  build_evpn_type3_prefix (&p, vpn->originator_ip);
  delete_evpn_route (bgp, vpn, &p);
}

/*
 * There is a tunnel endpoint IP address change for this VNI,
 * need to re-advertise routes with the new nexthop.
 */
static int
handle_tunnel_ip_change (struct bgp *bgp, struct bgpevpn *vpn,
                         struct in_addr originator_ip)
{
  struct prefix_evpn p;

  /* Need to withdraw type-3 route as the originator IP is part
   * of the key.
   */
  build_evpn_type3_prefix (&p, vpn->originator_ip);
  delete_evpn_route (bgp, vpn, &p);

  /* Update the tunnel IP and re-advertise all routes for this VNI. */
  vpn->originator_ip = originator_ip;
  return update_routes_for_vni (bgp, vpn);
}

/*
 * Given a route entry and a VNI, see if this route entry should be
 * imported into the VNI i.e., RTs match.
 */
static int
is_route_matching_for_vni (struct bgp *bgp, struct bgpevpn *vpn,
                           struct bgp_info *ri)
{
  struct attr *attr = ri->attr;
  struct ecommunity *ecom;
  int i;

  assert (attr);
  /* Route should have valid RT to be even considered. */
  if (!(attr->flag & ATTR_FLAG_BIT (BGP_ATTR_EXT_COMMUNITIES)))
    return 0;

  ecom = attr->extra->ecommunity;
  if (!ecom || !ecom->size)
    return 0;

  /* For each extended community RT, see if it matches this VNI. If any RT
   * matches, we're done.
   */
  for (i = 0; i < ecom->size; i++)
    {
      u_char *pnt;
      u_char type, sub_type;
      struct ecommunity_val *eval;
      struct ecommunity_val eval_tmp;
      struct irt_node *irt;

      /* Only deal with RTs */
      pnt = (ecom->val + (i * ECOMMUNITY_SIZE));
      eval = (struct ecommunity_val *) (ecom->val + (i * ECOMMUNITY_SIZE));
      type = *pnt++;
      sub_type = *pnt++;
      if (sub_type != ECOMMUNITY_ROUTE_TARGET)
        continue;

      /* See if this RT matches specified VNIs import RTs */
      irt = lookup_import_rt (bgp, eval);
      if (irt && irt->vnis)
        if (is_vni_present_in_irt_vnis (irt->vnis, vpn))
          return 1;

      /* Also check for non-exact match. In this, we mask out the AS and
       * only check on the local-admin sub-field. This is to facilitate using
       * VNI as the RT for EBGP peering too.
       */
      irt = NULL;
      if (type == ECOMMUNITY_ENCODE_AS ||
          type == ECOMMUNITY_ENCODE_AS4)
        {
          memcpy (&eval_tmp, eval, ECOMMUNITY_SIZE);
          mask_ecom_global_admin (&eval_tmp, eval);
          irt = lookup_import_rt (bgp, &eval_tmp);
        }
      if (irt && irt->vnis)
        if (is_vni_present_in_irt_vnis (irt->vnis, vpn))
          return 1;
    }

  return 0;
}

/*
 * Install or uninstall routes of specified type that are appropriate for this VNI.
 */
static int
install_uninstall_routes_for_vni (struct bgp *bgp, struct bgpevpn *vpn,
                                  bgp_evpn_route_type rtype, int install)
{
  afi_t afi;
  safi_t safi;
  struct bgp_node *rd_rn, *rn;
  struct bgp_table *table;
  struct bgp_info *ri;
  int ret;

  afi = AFI_L2VPN;
  safi = SAFI_EVPN;

  /* TODO: We're walking entire table, this should be optimized later. */
  /* EVPN routes are a 2-level table. */
  /* Note: We cannot just look at the routes for the VNI's RD - remote routes
   * applicable for this VNI could have any RD.
   */
  for (rd_rn = bgp_table_top(bgp->rib[afi][safi]); rd_rn; rd_rn = bgp_route_next (rd_rn))
    {
      table = (struct bgp_table *)(rd_rn->info);
      if (!table)
        continue;

      for (rn = bgp_table_top (table); rn; rn = bgp_route_next (rn))
        {
          struct prefix_evpn *evp = (struct prefix_evpn *)&rn->p;

          if (evp->prefix.route_type != rtype)
            continue;

          for (ri = rn->info; ri; ri = ri->next)
            {
              if (!(CHECK_FLAG (ri->flags, BGP_INFO_SELECTED)
                    && ri->type == ZEBRA_ROUTE_BGP
                    && ri->sub_type == BGP_ROUTE_NORMAL))
                continue;

              if (is_route_matching_for_vni (bgp, vpn, ri))
                {
                  if (rtype == BGP_EVPN_MAC_IP_ROUTE)
                    ret = bgp_zebra_send_remote_mac (bgp, vpn, evp,
                                           ri->attr->nexthop, install);
                  else
                    ret = bgp_zebra_send_remote_vtep (bgp, vpn, evp,
                                                      install);
                  if (ret)
                    {
                      zlog_err ("%u: Failed to %s EVPN %s route in VNI %u",
                                bgp->vrf_id, install ? "install" : "uninstall",
                                rtype == BGP_EVPN_MAC_IP_ROUTE ? \
                                "MACIP" : "IMET", vpn->vni);
                      return ret;
                    }
                }
            }
        }
    }

  return 0;
}

/*
 * VNI is "live", install any existing remote routes for this VNI.
 */
static int
install_routes_for_vni (struct bgp *bgp, struct bgpevpn *vpn)
{
  int ret;

  /* Install type-3 routes followed by type-2 routes - the ones applicable
   * for this VNI.
   */
  ret = install_uninstall_routes_for_vni (bgp, vpn, BGP_EVPN_IMET_ROUTE, 1);
  if (ret)
    return ret;

  return install_uninstall_routes_for_vni (bgp, vpn, BGP_EVPN_MAC_IP_ROUTE, 1);
}

/*
 * Uninstall any existing remote routes for this VNI. One scenario in which
 * this is invoked is upon an import RT change.
 */
static int
uninstall_routes_for_vni (struct bgp *bgp, struct bgpevpn *vpn)
{
  int ret;

  /* Uninstall type-2 routes followed by type-3 routes - the ones applicable
   * for this VNI.
   */
  ret = install_uninstall_routes_for_vni (bgp, vpn, BGP_EVPN_MAC_IP_ROUTE, 0);
  if (ret)
    return ret;

  return install_uninstall_routes_for_vni (bgp, vpn, BGP_EVPN_IMET_ROUTE, 0);
}

/*
 * Install or uninstall route in matching VNIs (list).
 */
static int
install_uninstall_route_in_vnis (struct bgp *bgp, afi_t afi, safi_t safi,
                                 struct prefix_evpn *evp, struct bgp_info *ri,
                                 struct list *vnis, int install)
{
  struct bgpevpn *vpn;
  struct listnode *node, *nnode;

  for (ALL_LIST_ELEMENTS (vnis, node, nnode, vpn))
    {
      int ret;

      if (!is_vni_live (vpn))
        continue;

      if (evp->prefix.route_type == BGP_EVPN_MAC_IP_ROUTE)
        ret = bgp_zebra_send_remote_mac (bgp, vpn, evp,
                                         ri->attr->nexthop, install);
      else
        ret = bgp_zebra_send_remote_vtep (bgp, vpn, evp, install);

      if (ret)
        {
          zlog_err ("%u: Failed to %s EVPN %s route in VNI %u",
                    bgp->vrf_id, install ? "install" : "uninstall",
                    evp->prefix.route_type == BGP_EVPN_MAC_IP_ROUTE ? \
                    "MACIP" : "IMET", vpn->vni);
          return ret;
        }
    }

  return 0;
}

/*
 * Install or uninstall route for appropriate VNIs.
 */
static int
install_uninstall_evpn_route (struct bgp *bgp, afi_t afi, safi_t safi,
                              struct prefix *p, struct bgp_info *ri,
                              int install)
{
  struct prefix_evpn *evp = (struct prefix_evpn *)p;
  struct attr *attr = ri->attr;
  struct ecommunity *ecom;
  int i;

  assert (attr);

  /* We can only deal with type-2 and type-3 EVPN routes. */
  if (!(evp->prefix.route_type == BGP_EVPN_MAC_IP_ROUTE ||
        evp->prefix.route_type == BGP_EVPN_IMET_ROUTE))
    return 0;

  /* If we don't have Route Target, nothing much to do. */
  if (!(attr->flag & ATTR_FLAG_BIT (BGP_ATTR_EXT_COMMUNITIES)))
    return 0;

  ecom = attr->extra->ecommunity;
  if (!ecom || !ecom->size)
    return -1;

  /* For each extended community RT, see which VNIs match and install
   * the route into matching VNIs.
   */
  for (i = 0; i < ecom->size; i++)
    {
      u_char *pnt;
      u_char type, sub_type;
      struct ecommunity_val *eval;
      struct ecommunity_val eval_tmp;
      struct irt_node *irt;

      /* Only deal with RTs */
      pnt = (ecom->val + (i * ECOMMUNITY_SIZE));
      eval = (struct ecommunity_val *) (ecom->val + (i * ECOMMUNITY_SIZE));
      type = *pnt++;
      sub_type = *pnt++;
      if (sub_type != ECOMMUNITY_ROUTE_TARGET)
        continue;

      /* Are we interested in this RT? */
      irt = lookup_import_rt (bgp, eval);
      if (irt && irt->vnis)
        install_uninstall_route_in_vnis (bgp, afi, safi, evp,
                                         ri, irt->vnis, install);

      /* Also check for non-exact match. In this, we mask out the AS and
       * only check on the local-admin sub-field. This is to facilitate using
       * VNI as the RT for EBGP peering too.
       */
      irt = NULL;
      if (type == ECOMMUNITY_ENCODE_AS ||
          type == ECOMMUNITY_ENCODE_AS4)
        {
          memcpy (&eval_tmp, eval, ECOMMUNITY_SIZE);
          mask_ecom_global_admin (&eval_tmp, eval);
          irt = lookup_import_rt (bgp, &eval_tmp);
        }
      if (irt && irt->vnis)
        install_uninstall_route_in_vnis (bgp, afi, safi, evp,
                                         ri, irt->vnis, install);
    }

  return 0;
}

/*
 * Process received EVPN type-2 route (advertise or withdraw).
 */
static int
process_type2_route (struct peer *peer, afi_t afi, safi_t safi,
                     struct attr *attr, u_char *pfx, int psize,
                     u_int32_t addpath_id)
{
  struct prefix_rd prd;
  struct prefix_evpn p;
  u_char ipaddr_len;
  u_char macaddr_len;
#if 0
  vni_t vni;
#endif
  int ret;

  /* Type-2 route should be either 33 or 52 bytes:
   * RD (8), ESI (10), Eth Tag (4), MAC Addr Len (1),
   * MAC Addr (6), IP len (1), IP (0, 4 or 16),
   * MPLS Lbl1 (3), MPLS Lbl2 (0 or 3).
   */
  if (psize != 33 && psize != 37 && psize != 49 && psize != 52)
    {
      zlog_err ("%u:%s - Rx EVPN NLRI with invalid length %d",
                peer->bgp->vrf_id, peer->host, psize);
      return -1;
    }

  /* Make prefix_rd */
  prd.family = AF_UNSPEC;
  prd.prefixlen = 64;
  memcpy (&prd.val, pfx, 8);
  pfx += 8;

  /* Make EVPN prefix. */
  memset (&p, 0, sizeof (struct prefix_evpn));
  p.family = AF_ETHERNET;
  p.prefixlen = EVPN_TYPE_2_ROUTE_PREFIXLEN;
  p.prefix.route_type = BGP_EVPN_MAC_IP_ROUTE;

  /* Skip over Ethernet Seg Identifier for now. */
  pfx += 10;

  /* Skip over Ethernet Tag for now. */
  pfx += 4;

  /* Get the MAC Addr len */
  macaddr_len = *pfx++;
  if (macaddr_len != ETHER_ADDR_LEN * 8)
    {
      zlog_err ("%u:%s - Rx EVPN NLRI with invalid MAC length %d",
                peer->bgp->vrf_id, peer->host, macaddr_len);
      return -1;
    }

  /* Get the MAC Addr */
  memcpy (&p.prefix.mac.octet, pfx, ETHER_ADDR_LEN);
  pfx += ETHER_ADDR_LEN;

  /* Get the IP. */
  ipaddr_len = *pfx++;
  if (ipaddr_len == 0)
    p.prefix.ipa_type = IP_ADDR_NONE;
  else
    {
      if (ipaddr_len == 32)
        p.prefix.ipa_type = IP_ADDR_V4;
      else if (ipaddr_len == 128)
        p.prefix.ipa_type = IP_ADDR_V6;
      else
        {
          zlog_err ("%u:%s - Rx EVPN NLRI with invalid IP length %d",
                    peer->bgp->vrf_id, peer->host, ipaddr_len);
          return -1;
        }
      memcpy (&p.prefix.ip, pfx, ipaddr_len/8);
    }
#if 0
  pfx += ipaddr_len/8;

  /* Get the VNI */
  vni = *pfx;
#endif

  /* Process the route. */
  if (attr)
    ret = bgp_update (peer, (struct prefix *)&p, addpath_id, attr, afi, safi,
                      ZEBRA_ROUTE_BGP, BGP_ROUTE_NORMAL, &prd, NULL, 0);
  else
    ret = bgp_withdraw (peer, (struct prefix *)&p, addpath_id, attr, afi, safi,
                        ZEBRA_ROUTE_BGP, BGP_ROUTE_NORMAL, &prd, NULL);
  return ret;
}

/*
 * Process received EVPN type-3 route (advertise or withdraw).
 */
static int
process_type3_route (struct peer *peer, afi_t afi, safi_t safi,
                     struct attr *attr, u_char *pfx, int psize,
                     u_int32_t addpath_id)
{
  struct prefix_rd prd;
  struct prefix_evpn p;
  u_char ipaddr_len;
  int ret;

  /* Type-3 route should be either 17 or 29 bytes: RD (8), Eth Tag (4),
   * IP len (1) and IP (4 or 16).
   */
  if (psize != 17 && psize != 29)
    {
      zlog_err ("%u:%s - Rx EVPN NLRI with invalid length %d",
                peer->bgp->vrf_id, peer->host, psize);
      return -1;
    }

  /* Make prefix_rd */
  prd.family = AF_UNSPEC;
  prd.prefixlen = 64;
  memcpy (&prd.val, pfx, 8);
  pfx += 8;

  /* Make EVPN prefix. */
  memset (&p, 0, sizeof (struct prefix_evpn));
  p.family = AF_ETHERNET;
  p.prefixlen = EVPN_TYPE_3_ROUTE_PREFIXLEN;
  p.prefix.route_type = BGP_EVPN_IMET_ROUTE;

  /* Skip over Ethernet Tag for now. */
  pfx += 4;

  /* Get the IP. */
  ipaddr_len = *pfx++;
  if (ipaddr_len == 32)
    p.prefix.ipa_type = IP_ADDR_V4;
  else if (ipaddr_len == 128)
    p.prefix.ipa_type = IP_ADDR_V6;
  else
    {
      zlog_err ("%u:%s - Rx EVPN NLRI with invalid IP length %d",
                peer->bgp->vrf_id, peer->host, ipaddr_len);
      return -1;
    }
  memcpy (&p.prefix.ip, pfx, ipaddr_len/8);

  /* Process the route. */
  if (attr)
    ret = bgp_update (peer, (struct prefix *)&p, addpath_id, attr, afi, safi,
                      ZEBRA_ROUTE_BGP, BGP_ROUTE_NORMAL, &prd, NULL, 0);
  else
    ret = bgp_withdraw (peer, (struct prefix *)&p, addpath_id, attr, afi, safi,
                        ZEBRA_ROUTE_BGP, BGP_ROUTE_NORMAL, &prd, NULL);
  return ret;
}

/*
 * Public functions.
 */

/*
 * Function to convert evpn route to string.
 * NOTE: We don't use prefix2str as the output here is a bit different.
 */
char *
bgp_evpn_route2str (struct prefix_evpn *p, char *buf, int len)
{
  char buf1[MACADDR_STRLEN];
  char buf2[PREFIX2STR_BUFFER];

  if (p->prefix.route_type == BGP_EVPN_IMET_ROUTE)
    {
      snprintf (buf, len, "[%d]:[0]:[%d]:[%s]",
                p->prefix.route_type, IS_EVPN_PREFIX_IPADDR_V4(p) ? \
                IPV4_MAX_BYTELEN : IPV6_MAX_BYTELEN,
                inet_ntoa(p->prefix.ip.v4_addr));
    }
  if (p->prefix.route_type == BGP_EVPN_MAC_IP_ROUTE)
    {
      if (IS_EVPN_PREFIX_IPADDR_NONE(p))
        snprintf (buf, len, "[%d]:[0]:[0]:[%d]:[%s]",
                  p->prefix.route_type, ETHER_ADDR_LEN,
                  mac2str (&p->prefix.mac, buf1, sizeof(buf1)));
      else
        {
          u_char family;

          family = IS_EVPN_PREFIX_IPADDR_V4(p) ? \
                   AF_INET : AF_INET6;
          snprintf (buf, len, "[%d]:[0]:[0]:[%d]:[%s]:[%d]:[%s]",
                    p->prefix.route_type, ETHER_ADDR_LEN,
                    mac2str (&p->prefix.mac, buf1, sizeof(buf1)),
                    family == AF_INET ? IPV4_MAX_BYTELEN : IPV6_MAX_BYTELEN,
                    inet_ntop (family, &p->prefix.ip.addr,
                               buf2, PREFIX2STR_BUFFER));
        }
    }

  return(buf);
}

/*
 * Map the RTs (configured or automatically derived) of a VNI to the VNI.
 * The mapping will be used during route processing.
 */
void
bgp_evpn_map_vni_to_its_rts (struct bgp *bgp, struct bgpevpn *vpn)
{
  int i;
  struct ecommunity *ecom;
  struct ecommunity_val *eval;

  ecom = vpn->import_rtl;
  if (!ecom || !ecom->size)
    return;

  for (i = 0; i < ecom->size; i++)
    {
      eval = (struct ecommunity_val *) (ecom->val + (i * ECOMMUNITY_SIZE));
      map_vni_to_rt (bgp, vpn, eval);
    }
}

/*
 * Map the RTs (configured or automatically derived) of a VNI to the VNI.
 * The mapping will be used during route processing.
 */
void
bgp_evpn_unmap_vni_from_its_rts (struct bgp *bgp, struct bgpevpn *vpn)
{
  int i;
  struct ecommunity *ecom;
  struct ecommunity_val *eval;

  ecom = vpn->import_rtl;
  if (!ecom || !ecom->size)
    return;

  for (i = 0; i < ecom->size; i++)
    {
      struct irt_node *irt;
      struct ecommunity_val eval_tmp;

      eval = (struct ecommunity_val *) (ecom->val + (i * ECOMMUNITY_SIZE));
      /* If using "automatic" RT, we only care about the local-admin sub-field.
       * This is to facilitate using VNI as the RT for EBGP peering too.
       */
      memcpy (&eval_tmp, eval, ECOMMUNITY_SIZE);
      if (!is_import_rt_configured (vpn))
        mask_ecom_global_admin (&eval_tmp, eval);

      irt = lookup_import_rt (bgp, &eval_tmp);
      if (irt)
        unmap_vni_from_rt (bgp, vpn, irt);
    }
}

/*
 * Derive Import RT automatically for VNI and map VNI to RT.
 * The mapping will be used during route processing.
 */
void
bgp_evpn_derive_auto_rt_import (struct bgp *bgp, struct bgpevpn *vpn)
{
  form_auto_rt (bgp, vpn, &vpn->import_rtl);
  UNSET_FLAG (vpn->flags, VNI_FLAG_IMPRT_CFGD);

  /* Map RT to VNI */
  bgp_evpn_map_vni_to_its_rts (bgp, vpn);
}

/*
 * Derive Export RT automatically for VNI.
 */
void
bgp_evpn_derive_auto_rt_export (struct bgp *bgp, struct bgpevpn *vpn)
{
  form_auto_rt (bgp, vpn, &vpn->export_rtl);
  UNSET_FLAG (vpn->flags, VNI_FLAG_EXPRT_CFGD);
}

/*
 * Derive RD automatically for VNI using passed information - it
 * is of the form RouterId:VNI.
 */
void
bgp_evpn_derive_auto_rd (struct bgp *bgp, struct bgpevpn *vpn)
{
  char buf[100];

  vpn->prd.family = AF_UNSPEC;
  vpn->prd.prefixlen = 64;
  sprintf (buf, "%s:%u", inet_ntoa (bgp->router_id), vpn->vni);
  str2prefix_rd (buf, &vpn->prd);
  UNSET_FLAG (vpn->flags, VNI_FLAG_RD_CFGD);
}

/*
 * Lookup VNI.
 */
struct bgpevpn *
bgp_evpn_lookup_vni (struct bgp *bgp, vni_t vni)
{
  struct bgpevpn *vpn;
  struct bgpevpn tmp;

  memset(&tmp, 0, sizeof(struct bgpevpn));
  tmp.vni = vni;
  vpn = hash_lookup (bgp->vnihash, &tmp);
  return vpn;
}

/*
 * Create a new vpn - invoked upon configuration or zebra notification.
 */
struct bgpevpn *
bgp_evpn_new (struct bgp *bgp, vni_t vni, struct in_addr originator_ip)
{
  struct bgpevpn *vpn;

  if (!bgp)
    return NULL;

  vpn = XCALLOC (MTYPE_BGP_EVPN, sizeof (struct bgpevpn));
  if (!vpn)
    return NULL;

  /* Set values - RD and RT set to defaults. */
  vpn->vni = vni;
  vpn->originator_ip = originator_ip;
  derive_rd_rt_for_vni (bgp, vpn);

  /* Add to hash */
  if (!hash_get(bgp->vnihash, vpn, hash_alloc_intern))
    {
      XFREE(MTYPE_BGP_EVPN, vpn);
      return NULL;
    }
  QOBJ_REG (vpn, bgpevpn);
  return vpn;
}

/*
 * Free a given VPN - called in multiple scenarios such as zebra
 * notification, configuration being deleted, advertise-vni disabled etc.
 * This just frees appropriate memory, caller should have taken other
 * needed actions.
 */
void
bgp_evpn_free (struct bgp *bgp, struct bgpevpn *vpn)
{
  bgp_evpn_unmap_vni_from_its_rts (bgp, vpn);
  ecommunity_free (&vpn->import_rtl);
  ecommunity_free (&vpn->export_rtl);
  hash_release (bgp->vnihash, vpn);
  QOBJ_UNREG (vpn);
  XFREE(MTYPE_BGP_EVPN, vpn);
}

/*
 * Encode EVPN prefix in Update (MP_REACH)
 */
void
bgp_evpn_encode_prefix (struct stream *s, struct prefix *p,
                        struct prefix_rd *prd, int addpath_encode,
                        u_int32_t addpath_tx_id)
{
  struct prefix_evpn *evp = (struct prefix_evpn *)p;

  if (addpath_encode)
    stream_putl (s, addpath_tx_id);

  /* Route type */
  stream_putc (s, evp->prefix.route_type);

  switch (evp->prefix.route_type)
    {
      case BGP_EVPN_IMET_ROUTE:
        stream_putc (s, 17); // TODO: Hardcoded for now
        stream_put (s, prd->val, 8); /* RD */
        stream_putl (s, 0); /* Ethernet Tag ID */
        stream_putc (s, 32); /* IP address Length */
        /* Originating Router's IP Addr */
        stream_put_in_addr (s, &evp->prefix.ip.v4_addr);
        break;

      case BGP_EVPN_MAC_IP_ROUTE:
        stream_putc (s, 33); // TODO: Hardcoded for now
        stream_put (s, prd->val, 8); /* RD */
        stream_put (s, 0, 10); /* ESI */
        stream_putl (s, 0); /* Ethernet Tag ID */
        stream_putc (s, ETHER_ADDR_LEN*8); /* Mac Addr Len */
        stream_put (s, evp->prefix.mac.octet, ETHER_ADDR_LEN); /* Mac Addr */
        stream_putc (s, 0); /* IP address Length */
        stream_put (s, &evp->prefix.vni, 3); /* VNI */
        break;

      default:
        break;
    }
}

/*
 * Perform sanity check on EVPN NLRI.
 * TODO: Not yet implemented.
 */
int
bgp_evpn_nlri_sanity_check (struct peer *peer, int afi, safi_t safi,
                            u_char *pnt, bgp_size_t length, int *numpfx)
{
  return 0;
}

/*
 * Process EVPN NLRI. Invoke functions based on EVPN route type that will
 * do necessary action to create/update/delete route and schedule for
 * processing.
 */
int
bgp_evpn_nlri_parse (struct peer *peer, struct attr *attr, struct bgp_nlri *packet)
{
  u_char *pnt;
  u_char *lim;
  afi_t afi;
  safi_t safi;
  u_int32_t addpath_id;
  int addpath_encoded;
  int psize = 0;
  u_char rtype;
  u_char rlen;
  struct prefix p;

  /* Check peer status. */
  if (peer->status != Established)
    {
      zlog_err ("%u:%s - EVPN update received in state %d",
                peer->bgp->vrf_id, peer->host, peer->status);
      return -1;
    }

  /* Start processing the NLRI - there may be multiple in the MP_REACH */
  pnt = packet->nlri;
  lim = pnt + packet->length;
  afi = packet->afi;
  safi = packet->safi;
  addpath_id = 0;

  addpath_encoded = (CHECK_FLAG (peer->af_cap[afi][safi], PEER_CAP_ADDPATH_AF_RX_ADV) &&
                     CHECK_FLAG (peer->af_cap[afi][safi], PEER_CAP_ADDPATH_AF_TX_RCV));

#define VPN_PREFIXLEN_MIN_BYTES (3 + 8) /* label + RD */
  for (; pnt < lim; pnt += psize)
    {
      /* Clear prefix structure. */
      memset (&p, 0, sizeof (struct prefix));

      /* Deal with path-id if AddPath is supported. */
      if (addpath_encoded)
        {
          /* When packet overflow occurs return immediately. */
          if (pnt + BGP_ADDPATH_ID_LEN > lim)
            return -1;

          addpath_id = ntohl(*((uint32_t*) pnt));
          pnt += BGP_ADDPATH_ID_LEN;
        }

      /* All EVPN NLRI types start with type and length. */
      if (pnt + 2 > lim)
        return -1;

      rtype = *pnt++;
      psize = rlen = *pnt++;

      /* When packet overflow occur return immediately. */
      if (pnt + psize > lim)
        return -1;

      switch (rtype)
        {
          case BGP_EVPN_IMET_ROUTE:
            if (process_type3_route (peer, afi, safi, attr,
                                     pnt, psize, addpath_id))
              {
                zlog_err ("%u:%s - Error in processing EVPN type-3 NLRI size %d",
                          peer->bgp->vrf_id, peer->host, psize);
                return -1;
              }
            break;

          case BGP_EVPN_MAC_IP_ROUTE:
            if (process_type2_route (peer, afi, safi, attr,
                                     pnt, psize, addpath_id))
              {
                zlog_err ("%u:%s - Error in processing EVPN type-2 NLRI size %d",
                          peer->bgp->vrf_id, peer->host, psize);
                return -1;
              }
            break;

          default:
            break;
        }

    }

  /* Packet length consistency check. */
  if (pnt != lim)
    return -1;

  return 0;
}

/*
 * Install EVPN route into zebra, if appropriate. The route may need to
 * be installed in multiple VNIs.
 */
int
bgp_evpn_install_route (struct bgp *bgp, afi_t afi, safi_t safi,
                        struct prefix *p, struct bgp_info *ri)
{
  return install_uninstall_evpn_route (bgp, afi, safi, p, ri, 1);
}

/*
 * Uninstall EVPN route from zebra, if appropriate. The route may need to
 * be uninstalled from multiple VNIs.
 */
int
bgp_evpn_uninstall_route (struct bgp *bgp, afi_t afi, safi_t safi,
                          struct prefix *p, struct bgp_info *ri)
{
  return install_uninstall_evpn_route (bgp, afi, safi, p, ri, 0);
}

/*
 * Handle change to router id.
 * - Update local VNI cache with new router id in RD
 * - Update evpn type 3 route by removing old RD and adding the new RD.
 * This should send withdraw with old RD and update with new RD to peers.
 */
void
bgp_evpn_handle_router_id_update (struct bgp *bgp, int withdraw)
{
  if (withdraw)
    hash_iterate (bgp->vnihash,
                  (void (*) (struct hash_backet *, void *))
                  withdraw_router_id_vni, bgp);
  else
    hash_iterate (bgp->vnihash,
                  (void (*) (struct hash_backet *, void *))
                  update_router_id_vni, bgp);
  return;
}

/*
 * Install routes for this VNI. Invoked upon change to Import RT.
 */
int
bgp_evpn_install_routes (struct bgp *bgp, struct bgpevpn *vpn)
{
  return install_routes_for_vni (bgp, vpn);
}

/*
 * Uninstall all routes installed for this VNI. Invoked upon change
 * to Import RT.
 */
int
bgp_evpn_uninstall_routes (struct bgp *bgp, struct bgpevpn *vpn)
{
  return uninstall_routes_for_vni (bgp, vpn);
}

/*
 * Handle change to export RT - update and advertise local routes.
 */
int
bgp_evpn_handle_export_rt_change (struct bgp *bgp, struct bgpevpn *vpn)
{
  return update_routes_for_vni (bgp, vpn);
}

/*
 * Handle add of a local MAC.
 */
int
bgp_evpn_local_macip_add (struct bgp *bgp, vni_t vni,
                          struct ethaddr *mac)
{
  struct bgpevpn *vpn;
  struct prefix_evpn p;

  if (!bgp->vnihash)
    {
      zlog_err ("%u: VNI hash not created", bgp->vrf_id);
      return -1;
    }

  if (vni > UINT16_MAX)
    {
      zlog_err ("%u: VNI %u too large, cannot be handled by EVPN",
                bgp->vrf_id, vni);
      return -1;
    }

  /* Lookup VNI hash - should exist. */
  vpn = bgp_evpn_lookup_vni (bgp, vni);
  if (!vpn || !is_vni_live (vpn))
    {
      zlog_warn ("%u: VNI hash entry for VNI %u %s at MACIP ADD",
                 bgp->vrf_id, vni, vpn ? "not live" : "not found");
      return -1;
    }

  /* Create EVPN type-2 route and schedule for processing. */
  build_evpn_type2_prefix (&p, mac, vpn->vni);
  if (update_evpn_route (bgp, vpn, &p))
    {
      char buf[MACADDR_STRLEN];

      zlog_err ("%u:Failed to create Type-2 route, VNI %u MAC %s",
                bgp->vrf_id, vpn->vni, mac2str (mac, buf, sizeof (buf)));
      return -1;
    }

  return 0;
}

/*
 * Handle del of a local MAC.
 */
int
bgp_evpn_local_macip_del (struct bgp *bgp, vni_t vni,
                          struct ethaddr *mac)
{
  struct bgpevpn *vpn;
  struct prefix_evpn p;

  if (!bgp->vnihash)
    {
      zlog_err ("%u: VNI hash not created", bgp->vrf_id);
      return -1;
    }

  if (vni > UINT16_MAX)
    {
      zlog_err ("%u: VNI %u too large, cannot be handled by EVPN",
                bgp->vrf_id, vni);
      return -1;
    }

  /* Lookup VNI hash - should exist. */
  vpn = bgp_evpn_lookup_vni (bgp, vni);
  if (!vpn || !is_vni_live (vpn))
    {
      zlog_warn ("%u: VNI hash entry for VNI %u %s at MACIP DEL",
                 bgp->vrf_id, vni, vpn ? "not live" : "not found");
      return -1;
    }

  /* Remove EVPN type-2 route and schedule for processing. */
  build_evpn_type2_prefix (&p, mac, vpn->vni);
  delete_evpn_route (bgp, vpn, &p);

  return 0;
}

/*
 * Handle add (or update) of a local VNI. The only VNI change we care
 * about is change to local-tunnel-ip.
 * TODO: Cannot handle VNI larger than UINT16_MAX
 */
int
bgp_evpn_local_vni_add (struct bgp *bgp, vni_t vni, struct in_addr originator_ip)
{
  struct bgpevpn *vpn;
  struct prefix_evpn p;

  if (!bgp->vnihash)
    {
      zlog_err ("%u: VNI hash not created", bgp->vrf_id);
      return -1;
    }

  if (vni > UINT16_MAX)
    {
      zlog_err ("%u: VNI %u too large, cannot be handled by EVPN",
                bgp->vrf_id, vni);
      return -1;
    }

  /* Lookup VNI. If present and no change, exit. */
  vpn = bgp_evpn_lookup_vni (bgp, vni);
  if (vpn && is_vni_live (vpn))
    {
      if (IPV4_ADDR_SAME (&vpn->originator_ip, &originator_ip))
        /* Probably some other param has changed that we don't care about. */
        return 0;

      /* Local tunnel endpoint IP address has changed */
      return handle_tunnel_ip_change (bgp, vpn, originator_ip);
    }

  /* Create or update as appropriate. */
  if (!vpn)
    {
      vpn = bgp_evpn_new (bgp, vni, originator_ip);
      if (!vpn)
        {
          zlog_err ("%u: Failed to allocate VNI entry for VNI %u - at Add",
                    bgp->vrf_id, vni);
          return -1;
        }
    }

  /* Mark as "live" */
  SET_FLAG (vpn->flags, VNI_FLAG_LIVE);

  /* Create EVPN type-3 route and schedule for processing. */
  build_evpn_type3_prefix (&p, vpn->originator_ip);
  if (update_evpn_route (bgp, vpn, &p))
    {
      zlog_err ("%u: Type3 route creation failure for VNI %u",
                bgp->vrf_id, vni);
      return -1;
    }

  /* If we have learnt and retained remote routes (VTEPs, MACs) for this VNI,
   * install them.
   */
  install_routes_for_vni (bgp, vpn);

  return 0;
}

/*
 * Handle del of a local VNI.
 */
int
bgp_evpn_local_vni_del (struct bgp *bgp, vni_t vni)
{
  struct bgpevpn *vpn;

  if (!bgp->vnihash)
    {
      zlog_err ("%u: VNI hash not created", bgp->vrf_id);
      return -1;
    }

  /* Locate VNI hash */
  vpn = bgp_evpn_lookup_vni (bgp, vni);
  if (!vpn)
    {
      zlog_warn ("%u: VNI hash entry for VNI %u not found at DEL",
                 bgp->vrf_id, vni);
      return 0;
    }

  /* Remove all local EVPN routes and schedule for processing (to
   * withdraw from peers).
   */
  delete_routes_for_vni (bgp, vpn);

  /* Clear "live" flag and see if hash needs to be freed. */
  UNSET_FLAG (vpn->flags, VNI_FLAG_LIVE);
  if (!is_vni_configured (vpn))
    bgp_evpn_free (bgp, vpn);

  return 0;
}

/*
 * Initialization for EVPN. Create VNI hash table, hash for RT to VNI.
 */
void
bgp_evpn_init (struct bgp *bgp)
{
  bgp->vnihash = hash_create(vni_hash_key_make, vni_hash_cmp);
  bgp->import_rt_hash = hash_create(import_rt_hash_key_make, import_rt_hash_cmp);
}

/*
 * Cleanup EVPN information on disable - Need to delete and withdraw
 * EVPN routes from peers.
 */
void
bgp_evpn_cleanup_on_disable (struct bgp *bgp)
{
  hash_iterate (bgp->vnihash,
                (void (*) (struct hash_backet *, void *))
                cleanup_vni_on_disable, bgp);
}

/*
 * Cleanup EVPN information - invoked at the time of bgpd exit or when the
 * BGP instance (default) is being freed.
 */
void
bgp_evpn_cleanup (struct bgp *bgp)
{
  hash_iterate (bgp->vnihash,
                (void (*) (struct hash_backet *, void *))
                free_vni_entry, bgp);
  hash_free(bgp->import_rt_hash);
  bgp->import_rt_hash = NULL;
  hash_free(bgp->vnihash);
  bgp->vnihash = NULL;
}
