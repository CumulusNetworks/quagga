/* Kernel routing table updates using netlink over GNU/Linux system.
 * Copyright (C) 1997, 98, 99 Kunihiro Ishiguro
 *
 * This file is part of GNU Zebra.
 *
 * GNU Zebra is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * GNU Zebra is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with GNU Zebra; see the file COPYING.  If not, write to the Free
 * Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.  
 */

#include <zebra.h>
#include <net/if_arp.h>

/* Hack for GNU libc version 2. */
#ifndef MSG_TRUNC
#define MSG_TRUNC      0x20
#endif /* MSG_TRUNC */

#include "linklist.h"
#include "if.h"
#include "log.h"
#include "prefix.h"
#include "connected.h"
#include "table.h"
#include "memory.h"
#include "zebra_memory.h"
#include "rib.h"
#include "thread.h"
#include "privs.h"
#include "nexthop.h"
#include "vrf.h"
#include "mpls.h"

#include "zebra/zserv.h"
#include "zebra/zebra_ns.h"
#include "zebra/zebra_vrf.h"
#include "zebra/rt.h"
#include "zebra/redistribute.h"
#include "zebra/interface.h"
#include "zebra/debug.h"
#include "zebra/rtadv.h"
#include "zebra/zebra_ptm.h"
#include "zebra/zebra_mroute.h"
#include "zebra/zebra_mpls.h"
#include "zebra/kernel_netlink.h"
#include "zebra/rt_netlink.h"
#include "zebra/zebra_vxlan.h"

/* TODO - Temporary definitions, need to refine. */
/* This needs to be addressed in a better way. */
#ifndef AF_MPLS
#define AF_MPLS 28
#endif

#ifndef RTA_VIA
#define RTA_VIA		18
#endif

#ifndef RTA_NEWDST
#define RTA_NEWDST	19
#endif

#ifndef RTA_ENCAP_TYPE
#define RTA_ENCAP_TYPE	21
#endif

#ifndef RTA_ENCAP
#define RTA_ENCAP	22
#endif

#ifndef RTA_EXPIRES
#define RTA_EXPIRES     23
#endif

#ifndef LWTUNNEL_ENCAP_MPLS
#define LWTUNNEL_ENCAP_MPLS  1
#endif

#ifndef MPLS_IPTUNNEL_DST
#define MPLS_IPTUNNEL_DST  1
#endif

#ifndef NDA_MASTER
#define NDA_MASTER   9
#endif

#ifndef NTF_SELF
#define NTF_SELF     0x02
#endif

#ifndef NDA_VLAN
#define NDA_VLAN     5
#endif
/* End of temporary definitions */

#ifndef NLMSG_TAIL
#define NLMSG_TAIL(nmsg) \
        ((struct rtattr *) (((u_char *) (nmsg)) + NLMSG_ALIGN((nmsg)->nlmsg_len)))
#endif

#ifndef RTA_TAIL
#define RTA_TAIL(rta) \
        ((struct rtattr *) (((u_char *) (rta)) + RTA_ALIGN((rta)->rta_len)))
#endif

static vlanid_t filter_vlan = 0;

struct gw_family_t
{
  u_int16_t     filler;
  u_int16_t     family;
  union g_addr  gate;
};

static inline int is_selfroute(int proto)
{
  if ((proto == RTPROT_BGP) || (proto == RTPROT_OSPF) ||
      (proto == RTPROT_STATIC) || (proto == RTPROT_ZEBRA) ||
      (proto == RTPROT_ISIS) || (proto == RTPROT_RIPNG)) {
    return 1;
  }

  return 0;
}

static inline int get_rt_proto(int proto)
{
  switch (proto) {
  case ZEBRA_ROUTE_BGP:
    proto = RTPROT_BGP;
    break;
  case ZEBRA_ROUTE_OSPF:
  case ZEBRA_ROUTE_OSPF6:
    proto = RTPROT_OSPF;
    break;
  case ZEBRA_ROUTE_STATIC:
    proto = RTPROT_STATIC;
    break;
  case ZEBRA_ROUTE_ISIS:
    proto = RTPROT_ISIS;
    break;
  case ZEBRA_ROUTE_RIP:
    proto = RTPROT_RIP;
    break;
  case ZEBRA_ROUTE_RIPNG:
    proto = RTPROT_RIPNG;
    break;
  default:
    proto = RTPROT_ZEBRA;
    break;
  }

  return proto;
}

/*
Pending: create an efficient table_id (in a tree/hash) based lookup)
 */
static vrf_id_t
vrf_lookup_by_table (u_int32_t table_id)
{
  struct zebra_vrf *zvrf;
  vrf_iter_t iter;

  for (iter = vrf_first (); iter != VRF_ITER_INVALID; iter = vrf_next (iter))
    {
      if ((zvrf = vrf_iter2info (iter)) == NULL ||
          (zvrf->table_id != table_id))
        continue;

      return zvrf->vrf_id;
    }

  return VRF_DEFAULT;
}

/* Lookup interface IPv4/IPv6 address. */
/* Looking up routing table by netlink interface. */
static int
netlink_routing_table (struct sockaddr_nl *snl, struct nlmsghdr *h,
                       ns_id_t ns_id)
{
  int len;
  struct rtmsg *rtm;
  struct rtattr *tb[RTA_MAX + 1];
  u_char flags = 0;
  struct prefix p;
  vrf_id_t vrf_id = VRF_DEFAULT;

  char anyaddr[16] = { 0 };

  int index;
  int table;
  int metric;
  u_int32_t mtu = 0;

  void *dest;
  void *gate;
  void *src;

  rtm = NLMSG_DATA (h);

  if (h->nlmsg_type != RTM_NEWROUTE)
    return 0;
  if (rtm->rtm_type != RTN_UNICAST)
    return 0;

  len = h->nlmsg_len - NLMSG_LENGTH (sizeof (struct rtmsg));
  if (len < 0)
    return -1;

  memset (tb, 0, sizeof tb);
  netlink_parse_rtattr (tb, RTA_MAX, RTM_RTA (rtm), len);

  if (rtm->rtm_flags & RTM_F_CLONED)
    return 0;
  if (rtm->rtm_protocol == RTPROT_REDIRECT)
    return 0;
  if (rtm->rtm_protocol == RTPROT_KERNEL)
    return 0;

  if (rtm->rtm_src_len != 0)
    return 0;

  /* We don't care about change notifications for the MPLS table. */
  /* TODO: Revisit this. */
  if (rtm->rtm_family == AF_MPLS)
    return 0;

  /* Table corresponding to route. */
  if (tb[RTA_TABLE])
    table = *(int *) RTA_DATA (tb[RTA_TABLE]);
  else
    table = rtm->rtm_table;

  /* Map to VRF */
  vrf_id = vrf_lookup_by_table(table);
  if (vrf_id == VRF_DEFAULT)
    {
      if (!is_zebra_valid_kernel_table(table) &&
          !is_zebra_main_routing_table(table))
        return 0;
    }

  /* Route which inserted by Zebra. */
  if (is_selfroute(rtm->rtm_protocol))
    flags |= ZEBRA_FLAG_SELFROUTE;

  index = 0;
  metric = 0;
  dest = NULL;
  gate = NULL;
  src = NULL;

  if (tb[RTA_OIF])
    index = *(int *) RTA_DATA (tb[RTA_OIF]);

  if (tb[RTA_DST])
    dest = RTA_DATA (tb[RTA_DST]);
  else
    dest = anyaddr;

  if (tb[RTA_PREFSRC])
    src = RTA_DATA (tb[RTA_PREFSRC]);

  if (tb[RTA_GATEWAY])
    gate = RTA_DATA (tb[RTA_GATEWAY]);

  if (tb[RTA_PRIORITY])
    metric = *(int *) RTA_DATA(tb[RTA_PRIORITY]);

  if (tb[RTA_METRICS])
    {
      struct rtattr *mxrta[RTAX_MAX+1];

      memset (mxrta, 0, sizeof mxrta);
      netlink_parse_rtattr (mxrta, RTAX_MAX, RTA_DATA(tb[RTA_METRICS]),
                            RTA_PAYLOAD(tb[RTA_METRICS]));

      if (mxrta[RTAX_MTU])
        mtu = *(u_int32_t *) RTA_DATA(mxrta[RTAX_MTU]);
    }

  if (rtm->rtm_family == AF_INET)
    {
      p.family = AF_INET;
      memcpy (&p.u.prefix4, dest, 4);
      p.prefixlen = rtm->rtm_dst_len;

      if (!tb[RTA_MULTIPATH])
	rib_add (AFI_IP, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL,
		 0, flags, &p, gate, src, index,
		 table, metric, mtu, 0);
      else
        {
          /* This is a multipath route */

          struct rib *rib;
          struct rtnexthop *rtnh =
            (struct rtnexthop *) RTA_DATA (tb[RTA_MULTIPATH]);

          len = RTA_PAYLOAD (tb[RTA_MULTIPATH]);

          rib = XCALLOC (MTYPE_RIB, sizeof (struct rib));
          rib->type = ZEBRA_ROUTE_KERNEL;
          rib->distance = 0;
          rib->flags = flags;
          rib->metric = metric;
          rib->mtu = mtu;
          rib->vrf_id = vrf_id;
          rib->table = table;
          rib->nexthop_num = 0;
          rib->uptime = time (NULL);

          for (;;)
            {
              if (len < (int) sizeof (*rtnh) || rtnh->rtnh_len > len)
                break;

              index = rtnh->rtnh_ifindex;
              gate = 0;
              if (rtnh->rtnh_len > sizeof (*rtnh))
                {
                  memset (tb, 0, sizeof (tb));
                  netlink_parse_rtattr (tb, RTA_MAX, RTNH_DATA (rtnh),
                                        rtnh->rtnh_len - sizeof (*rtnh));
                  if (tb[RTA_GATEWAY])
                    gate = RTA_DATA (tb[RTA_GATEWAY]);
                }

              if (gate)
                {
                  if (index)
                    rib_nexthop_ipv4_ifindex_add (rib, gate, src, index);
                  else
                    rib_nexthop_ipv4_add (rib, gate, src);
                }
              else
                rib_nexthop_ifindex_add (rib, index);

              len -= NLMSG_ALIGN(rtnh->rtnh_len);
              rtnh = RTNH_NEXT(rtnh);
            }

	  zserv_nexthop_num_warn(__func__, (const struct prefix *)&p,
				 rib->nexthop_num);
          if (rib->nexthop_num == 0)
            XFREE (MTYPE_RIB, rib);
          else
            rib_add_multipath (AFI_IP, SAFI_UNICAST, &p, rib);
        }
    }
  if (rtm->rtm_family == AF_INET6)
    {
      p.family = AF_INET6;
      memcpy (&p.u.prefix6, dest, 16);
      p.prefixlen = rtm->rtm_dst_len;

      rib_add (AFI_IP6, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL,
	       0, flags, &p, gate, src, index,
	       table, metric, mtu, 0);
    }

  return 0;
}

/* Routing information change from the kernel. */
static int
netlink_route_change_read_unicast (struct sockaddr_nl *snl, struct nlmsghdr *h,
				   ns_id_t ns_id)
{
  int len;
  struct rtmsg *rtm;
  struct rtattr *tb[RTA_MAX + 1];
  u_char zebra_flags = 0;
  struct prefix p;
  vrf_id_t vrf_id = VRF_DEFAULT;
  
  char anyaddr[16] = { 0 };

  int index;
  int table;
  int metric;
  u_int32_t mtu = 0;

  void *dest;
  void *gate;
  void *src;

  rtm = NLMSG_DATA (h);

  len = h->nlmsg_len - NLMSG_LENGTH (sizeof (struct rtmsg));

  memset (tb, 0, sizeof tb);
  netlink_parse_rtattr (tb, RTA_MAX, RTM_RTA (rtm), len);

  if (rtm->rtm_flags & RTM_F_CLONED)
    return 0;
  if (rtm->rtm_protocol == RTPROT_REDIRECT)
    return 0;
  if (rtm->rtm_protocol == RTPROT_KERNEL)
    return 0;

  if (is_selfroute(rtm->rtm_protocol) && h->nlmsg_type == RTM_NEWROUTE)
    return 0;
  if (is_selfroute(rtm->rtm_protocol))
    SET_FLAG(zebra_flags, ZEBRA_FLAG_SELFROUTE);

  if (rtm->rtm_src_len != 0)
    {
      zlog_warn ("netlink_route_change(): no src len");
      return 0;
    }

  /* Table corresponding to route. */
  if (tb[RTA_TABLE])
    table = *(int *) RTA_DATA (tb[RTA_TABLE]);
  else
    table = rtm->rtm_table;

  /* Map to VRF */
  vrf_id = vrf_lookup_by_table(table);
  if (vrf_id == VRF_DEFAULT)
    {
      if (!is_zebra_valid_kernel_table(table) &&
          !is_zebra_main_routing_table(table))
        return 0;
    }

  index = 0;
  metric = 0;
  dest = NULL;
  gate = NULL;
  src = NULL;

  if (tb[RTA_OIF])
    index = *(int *) RTA_DATA (tb[RTA_OIF]);

  if (tb[RTA_DST])
    dest = RTA_DATA (tb[RTA_DST]);
  else
    dest = anyaddr;

  if (tb[RTA_GATEWAY])
    gate = RTA_DATA (tb[RTA_GATEWAY]);

  if (tb[RTA_PREFSRC])
    src = RTA_DATA (tb[RTA_PREFSRC]);

  if (h->nlmsg_type == RTM_NEWROUTE)
    {
      if (tb[RTA_PRIORITY])
        metric = *(int *) RTA_DATA(tb[RTA_PRIORITY]);

      if (tb[RTA_METRICS])
        {
          struct rtattr *mxrta[RTAX_MAX+1];

          memset (mxrta, 0, sizeof mxrta);
          netlink_parse_rtattr (mxrta, RTAX_MAX, RTA_DATA(tb[RTA_METRICS]),
                                RTA_PAYLOAD(tb[RTA_METRICS]));

          if (mxrta[RTAX_MTU])
            mtu = *(u_int32_t *) RTA_DATA(mxrta[RTAX_MTU]);
        }
    }

  if (rtm->rtm_family == AF_INET)
    {
      p.family = AF_INET;
      memcpy (&p.u.prefix4, dest, 4);
      p.prefixlen = rtm->rtm_dst_len;

      if (IS_ZEBRA_DEBUG_KERNEL)
        {
          char buf[PREFIX_STRLEN];
          zlog_debug ("%s %s vrf %u",
                      nl_msg_type_to_str (h->nlmsg_type),
                      prefix2str (&p, buf, sizeof(buf)), vrf_id);
        }

      if (h->nlmsg_type == RTM_NEWROUTE)
        {
          if (!tb[RTA_MULTIPATH])
            rib_add (AFI_IP, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL,
		     0, 0, &p, gate, src, index,
		     table, metric, mtu, 0);
          else
            {
              /* This is a multipath route */

              struct rib *rib;
              struct rtnexthop *rtnh =
                (struct rtnexthop *) RTA_DATA (tb[RTA_MULTIPATH]);

              len = RTA_PAYLOAD (tb[RTA_MULTIPATH]);

              rib = XCALLOC (MTYPE_RIB, sizeof (struct rib));
              rib->type = ZEBRA_ROUTE_KERNEL;
              rib->distance = 0;
              rib->flags = 0;
              rib->metric = metric;
              rib->mtu = mtu;
              rib->vrf_id = vrf_id;
              rib->table = table;
              rib->nexthop_num = 0;
              rib->uptime = time (NULL);

              for (;;)
                {
                  if (len < (int) sizeof (*rtnh) || rtnh->rtnh_len > len)
                    break;

                  index = rtnh->rtnh_ifindex;
                  gate = 0;
                  if (rtnh->rtnh_len > sizeof (*rtnh))
                    {
                      memset (tb, 0, sizeof (tb));
                      netlink_parse_rtattr (tb, RTA_MAX, RTNH_DATA (rtnh),
                                            rtnh->rtnh_len - sizeof (*rtnh));
                      if (tb[RTA_GATEWAY])
                        gate = RTA_DATA (tb[RTA_GATEWAY]);
                    }

                  if (gate)
                    {
                      if (index)
                        rib_nexthop_ipv4_ifindex_add (rib, gate, src, index);
                      else
                        rib_nexthop_ipv4_add (rib, gate, src);
                    }
                  else
                    rib_nexthop_ifindex_add (rib, index);

                  len -= NLMSG_ALIGN(rtnh->rtnh_len);
                  rtnh = RTNH_NEXT(rtnh);
                }

	      zserv_nexthop_num_warn(__func__, (const struct prefix *)&p,
				     rib->nexthop_num);

              if (rib->nexthop_num == 0)
                XFREE (MTYPE_RIB, rib);
              else
                rib_add_multipath (AFI_IP, SAFI_UNICAST, &p, rib);
            }
        }
      else
        rib_delete (AFI_IP, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL, 0, zebra_flags,
		    &p, gate, index, table);
    }

  if (rtm->rtm_family == AF_INET6)
    {
      struct prefix p;

      p.family = AF_INET6;
      memcpy (&p.u.prefix6, dest, 16);
      p.prefixlen = rtm->rtm_dst_len;

      if (IS_ZEBRA_DEBUG_KERNEL)
        {
	  char buf[PREFIX_STRLEN];
          zlog_debug ("%s %s vrf %u",
                      nl_msg_type_to_str (h->nlmsg_type),
                      prefix2str (&p, buf, sizeof(buf)), vrf_id);
        }

      if (h->nlmsg_type == RTM_NEWROUTE)
        rib_add (AFI_IP6, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL,
		 0, 0, &p, gate, src, index,
		 table, metric, mtu, 0);
      else
        rib_delete (AFI_IP6, SAFI_UNICAST, vrf_id, ZEBRA_ROUTE_KERNEL,
		    0, zebra_flags, &p, gate, index, table);
    }

  return 0;
}

static struct mcast_route_data *mroute = NULL;

static int
netlink_route_change_read_multicast (struct sockaddr_nl *snl, struct nlmsghdr *h,
				     ns_id_t ns_id)
{
  int len;
  struct rtmsg *rtm;
  struct rtattr *tb[RTA_MAX + 1];
  struct mcast_route_data *m;
  struct mcast_route_data mr;
  int iif = 0;
  int count;
  int oif[256];
  int oif_count = 0;
  char sbuf[40];
  char gbuf[40];
  char oif_list[256] = "\0";
  vrf_id_t vrf = ns_id;

  if (mroute)
    m = mroute;
  else
    {
      memset (&mr, 0, sizeof (mr));
      m = &mr;
    }

  rtm = NLMSG_DATA (h);

  len = h->nlmsg_len - NLMSG_LENGTH (sizeof (struct rtmsg));

  memset (tb, 0, sizeof tb);
  netlink_parse_rtattr (tb, RTA_MAX, RTM_RTA (rtm), len);

  if (tb[RTA_IIF])
    iif = *(int *)RTA_DATA (tb[RTA_IIF]);

  if (tb[RTA_SRC])
    m->sg.src = *(struct in_addr *)RTA_DATA (tb[RTA_SRC]);

  if (tb[RTA_DST])
    m->sg.grp = *(struct in_addr *)RTA_DATA (tb[RTA_DST]);

  if ((RTA_EXPIRES <= RTA_MAX) && tb[RTA_EXPIRES])
    m->lastused = *(unsigned long long *)RTA_DATA (tb[RTA_EXPIRES]);

  if (tb[RTA_MULTIPATH])
    {
      struct rtnexthop *rtnh =
        (struct rtnexthop *)RTA_DATA (tb[RTA_MULTIPATH]);

      len = RTA_PAYLOAD (tb[RTA_MULTIPATH]);
      for (;;)
        {
          if (len < (int) sizeof (*rtnh) || rtnh->rtnh_len > len)
	    break;

	  oif[oif_count] = rtnh->rtnh_ifindex;
          oif_count++;

	  len -= NLMSG_ALIGN (rtnh->rtnh_len);
	  rtnh = RTNH_NEXT (rtnh);
        }
    }

  if (IS_ZEBRA_DEBUG_KERNEL)
    {
      struct interface *ifp;
      strcpy (sbuf, inet_ntoa (m->sg.src));
      strcpy (gbuf, inet_ntoa (m->sg.grp));
      for (count = 0; count < oif_count; count++)
	{
	  ifp = if_lookup_by_index_vrf (oif[count], vrf);
	  char temp[256];

	  sprintf (temp, "%s ", ifp->name);
	  strcat (oif_list, temp);
	}
      ifp = if_lookup_by_index_vrf (iif, vrf);
      zlog_debug ("MCAST %s (%s,%s) IIF: %s OIF: %s jiffies: %lld",
		  nl_msg_type_to_str (h->nlmsg_type), sbuf, gbuf, ifp->name, oif_list, m->lastused);
    }
  return 0;
}

int
netlink_route_change (struct sockaddr_nl *snl, struct nlmsghdr *h,
		      ns_id_t ns_id)
{
  int len;
  vrf_id_t vrf_id = ns_id;
  struct rtmsg *rtm;

  rtm = NLMSG_DATA (h);

  if (!(h->nlmsg_type == RTM_NEWROUTE || h->nlmsg_type == RTM_DELROUTE))
    {
      /* If this is not route add/delete message print warning. */
      zlog_warn ("Kernel message: %d vrf %u\n", h->nlmsg_type, vrf_id);
      return 0;
    }

  /* Connected route. */
  if (IS_ZEBRA_DEBUG_KERNEL)
    zlog_debug ("%s %s %s proto %s",
		nl_msg_type_to_str (h->nlmsg_type),
                nl_family_to_str (rtm->rtm_family),
                nl_rttype_to_str (rtm->rtm_type),
                nl_rtproto_to_str (rtm->rtm_protocol));

  if (rtm->rtm_family == AF_MPLS)
    return 0;

  len = h->nlmsg_len - NLMSG_LENGTH (sizeof (struct rtmsg));
  if (len < 0)
    return -1;

  switch (rtm->rtm_type)
    {
    case RTN_UNICAST:
      netlink_route_change_read_unicast (snl, h, ns_id);
      break;
    case RTN_MULTICAST:
      netlink_route_change_read_multicast (snl, h, ns_id);
      break;
    default:
      return 0;
      break;
    }

  return 0;
}

/* Routing table read function using netlink interface.  Only called
   bootstrap time. */
int
netlink_route_read (struct zebra_ns *zns)
{
  int ret;

  /* Get IPv4 routing table. */
  ret = netlink_request (AF_INET, RTM_GETROUTE, &zns->netlink_cmd, 0);
  if (ret < 0)
    return ret;
  ret = netlink_parse_info (netlink_routing_table, &zns->netlink_cmd, zns, 0);
  if (ret < 0)
    return ret;

  /* Get IPv6 routing table. */
  ret = netlink_request (AF_INET6, RTM_GETROUTE, &zns->netlink_cmd, 0);
  if (ret < 0)
    return ret;
  ret = netlink_parse_info (netlink_routing_table, &zns->netlink_cmd, zns, 0);
  if (ret < 0)
    return ret;

  return 0;
}

#ifndef NDA_RTA
#define NDA_RTA(r) \
        ((struct rtattr*)(((char*)(r)) + NLMSG_ALIGN(sizeof(struct ndmsg))))
#endif

static int
netlink_neigh_table (struct sockaddr_nl *snl, struct nlmsghdr *h,
                     ns_id_t ns_id)
{
  if (h->nlmsg_type != RTM_NEWNEIGH)
    return 0;

  return netlink_neigh_change (snl, h, ns_id);
}

int
netlink_neigh_change (struct sockaddr_nl *snl, struct nlmsghdr *h,
                      ns_id_t ns_id)
{
  int len;
  struct ndmsg *ndm;
  struct interface *ifp;
  struct zebra_if *zif;
  struct zebra_vrf *zvrf;
  struct rtattr *tb[NDA_MAX + 1];
  struct zebra_l2info_brslave *br_slave;
  struct interface *br_if;
  struct ethaddr mac;
  vlanid_t vid = 0;
  char buf[MACADDR_STRLEN];

  if (!(h->nlmsg_type == RTM_NEWNEIGH || h->nlmsg_type == RTM_DELNEIGH))
    return 0;

  /* Length validity. */
  len = h->nlmsg_len - NLMSG_LENGTH (sizeof (struct ndmsg));
  if (len < 0)
    return -1;

  /* We are interested only in AF_BRIDGE notifications. */
  ndm = NLMSG_DATA (h);
  if (ndm->ndm_family != AF_BRIDGE)
    return 0;

  /* The interface should exist. */
  ifp = if_lookup_by_index_per_ns (zebra_ns_lookup (NS_DEFAULT), ndm->ndm_ifindex);
  if (!ifp)
    return 0;

  /* Locate VRF corresponding to interface. We only process MAC notifications
   * if EVPN is enabled on this VRF.
   */
  zvrf = vrf_info_lookup(ifp->vrf_id);
  if (!zvrf || !EVPN_ENABLED(zvrf))
    return 0;
  if (!ifp->info)
    return 0;

  /* The interface should be something we're interested in. */
  if (!IS_ZEBRA_IF_BRIDGE_SLAVE(ifp))
    return 0;

  /* Drop "permanent" entries. */
  if (ndm->ndm_state & NUD_PERMANENT)
    return 0;

  zif = (struct zebra_if *)ifp->info;
  br_slave = (struct zebra_l2info_brslave *)zif->l2if;
  assert (br_slave);
  if ((br_if = br_slave->br_if) == NULL)
    {
      zlog_warn ("%s family %s IF %s(%u) brIF %u - no bridge master",
		 nl_msg_type_to_str (h->nlmsg_type),
                 nl_family_to_str (ndm->ndm_family),
                 ifp->name, ndm->ndm_ifindex, br_slave->bridge_ifindex);
      return 0;
    }

  /* Parse attributes and extract fields of interest. */
  memset (tb, 0, sizeof tb);
  netlink_parse_rtattr (tb, NDA_MAX, NDA_RTA (ndm), len);

  if (!tb[NDA_LLADDR])
    {
      zlog_warn ("%s family %s IF %s(%u) brIF %u - no LLADDR",
                 nl_msg_type_to_str (h->nlmsg_type),
                 nl_family_to_str (ndm->ndm_family),
                 ifp->name, ndm->ndm_ifindex, br_slave->bridge_ifindex);
      return 0;
    }

  if (RTA_PAYLOAD (tb[NDA_LLADDR]) != ETHER_ADDR_LEN)
    {
      zlog_warn ("%s family %s IF %s(%u) brIF %u - LLADDR is not MAC, len %ld",
                 nl_msg_type_to_str (h->nlmsg_type),
                 nl_family_to_str (ndm->ndm_family),
                 ifp->name, ndm->ndm_ifindex, br_slave->bridge_ifindex,
                 RTA_PAYLOAD (tb[NDA_LLADDR]));
      return 0;
    }

  memcpy (&mac, RTA_DATA (tb[NDA_LLADDR]), ETHER_ADDR_LEN);

  if ((NDA_VLAN <= NDA_MAX) && tb[NDA_VLAN])
    vid = *(u_int16_t *) RTA_DATA(tb[NDA_VLAN]);

  if (IS_ZEBRA_DEBUG_KERNEL)
    zlog_debug ("Rx %s family %s IF %s(%u) VLAN %u MAC %s",
                nl_msg_type_to_str (h->nlmsg_type),
                nl_family_to_str (ndm->ndm_family),
                ifp->name, ndm->ndm_ifindex, vid,
                mac2str (&mac, buf, sizeof (buf)));

  if (filter_vlan && vid != filter_vlan)
    return 0;

  /* If add or update, do accordingly if learnt on a "local" interface; if
   * the notification is over VxLAN, this has to be related to multi-homing,
   * so perform an implicit delete of any local entry (if it exists).
   */
  if (h->nlmsg_type == RTM_NEWNEIGH)
    {
      if (IS_ZEBRA_IF_VXLAN(ifp))
        return zebra_vxlan_check_del_local_mac (ifp, br_if, &mac, vid);

      return zebra_vxlan_local_mac_add_update (ifp, br_if, &mac, vid);
    }

  /* This is a delete notification. If notification is for a MAC over VxLAN,
   * check if it needs to be readded (refreshed); otherwise, handle delete of
   * MAC over "local" interface.
   */
  if (IS_ZEBRA_IF_VXLAN(ifp))
    return zebra_vxlan_check_readd_remote_mac (ifp, br_if, &mac, vid);

  return zebra_vxlan_local_mac_del (ifp, br_if, &mac, vid);
}

/*
 * Neighbor table read using netlink interface. This is invoked
 * at startup and we are currently concerned only about the
 * bridge FDB.
 */
int
netlink_neigh_read (struct zebra_ns *zns)
{
  int ret;

  /* Get bridge FDB table. */
  ret = netlink_request (AF_BRIDGE, RTM_GETNEIGH, &zns->netlink_cmd, 0);
  if (ret < 0)
    return ret;
  /* We are reading entire table. */
  filter_vlan = 0;
  ret = netlink_parse_info (netlink_neigh_table, &zns->netlink_cmd, zns, 0);

  return ret;
}

/*
 * Neighbor table read using netlink interface. This is for a specific
 * bridge and matching specific access VLAN (if VLAN-aware bridge).
 */
int
netlink_neigh_read_for_bridge (struct zebra_ns *zns, struct interface *ifp,
                               struct interface *br_if)
{
  struct
    {
      struct nlmsghdr   n;
      struct ifinfomsg  ifm;
      char              buf[256];
    } req;
  struct zebra_if *br_zif;
  struct zebra_if *zif;
  struct zebra_l2if_vxlan *zl2if;
  int ret = 0;

  memset (&req, 0, sizeof(req));
  req.n.nlmsg_len = NLMSG_LENGTH(sizeof(struct ifinfomsg));
  req.n.nlmsg_type = RTM_GETNEIGH;
  req.n.nlmsg_flags = NLM_F_REQUEST | NLM_F_DUMP;
  req.ifm.ifi_family = AF_BRIDGE;
  addattr32 (&req.n, sizeof(req), IFLA_MASTER, br_if->ifindex);

  /* Save VLAN we're filtering on, if needed. */
  br_zif = (struct zebra_if *) br_if->info;
  zif = (struct zebra_if *) ifp->info;
  zl2if = (struct zebra_l2if_vxlan *)zif->l2if;
  if (!zl2if)
    return -1;
  if (IS_ZEBRA_IF_BRIDGE_VLAN_AWARE(br_zif))
    filter_vlan = zl2if->access_vlan;
  ret = netlink_talk (netlink_neigh_table, &req.n,
                      &zns->netlink_cmd, zns);

  /* Reset VLAN filter. */
  filter_vlan = 0;
  return ret;
}

static void
_netlink_route_nl_add_gateway_info (u_char route_family, u_char gw_family,
                                    struct nlmsghdr *nlmsg,
                                    size_t req_size, int bytelen,
                                    struct nexthop *nexthop)
{
  if (route_family == AF_MPLS)
    {
      struct gw_family_t gw_fam;

      gw_fam.family = gw_family;
      if (gw_family == AF_INET)
        memcpy (&gw_fam.gate.ipv4, &nexthop->gate.ipv4, bytelen);
      else
        memcpy (&gw_fam.gate.ipv6, &nexthop->gate.ipv6, bytelen);
      addattr_l (nlmsg, req_size, RTA_VIA, &gw_fam.family, bytelen+2);
    }
  else
    {
      if (gw_family == AF_INET)
        addattr_l (nlmsg, req_size, RTA_GATEWAY, &nexthop->gate.ipv4, bytelen);
      else
        addattr_l (nlmsg, req_size, RTA_GATEWAY, &nexthop->gate.ipv6, bytelen);
    }
}

static void
_netlink_route_rta_add_gateway_info (u_char route_family, u_char gw_family,
                                     struct rtattr *rta, struct rtnexthop *rtnh,
                                     size_t req_size, int bytelen,
                                     struct nexthop *nexthop)
{
  if (route_family == AF_MPLS)
    {
      struct gw_family_t gw_fam;

      gw_fam.family = gw_family;
      if (gw_family == AF_INET)
        memcpy (&gw_fam.gate.ipv4, &nexthop->gate.ipv4, bytelen);
      else
        memcpy (&gw_fam.gate.ipv6, &nexthop->gate.ipv6, bytelen);
      rta_addattr_l (rta, req_size, RTA_VIA, &gw_fam.family, bytelen+2);
      rtnh->rtnh_len += RTA_LENGTH (bytelen + 2);
    }
  else
    {
      if (gw_family == AF_INET)
        rta_addattr_l (rta, req_size, RTA_GATEWAY, &nexthop->gate.ipv4, bytelen);
      else
        rta_addattr_l (rta, req_size, RTA_GATEWAY, &nexthop->gate.ipv6, bytelen);
      rtnh->rtnh_len += sizeof (struct rtattr) + bytelen;
    }
}

/* This function takes a nexthop as argument and adds
 * the appropriate netlink attributes to an existing
 * netlink message.
 *
 * @param routedesc: Human readable description of route type
 *                   (direct/recursive, single-/multipath)
 * @param bytelen: Length of addresses in bytes.
 * @param nexthop: Nexthop information
 * @param nlmsg: nlmsghdr structure to fill in.
 * @param req_size: The size allocated for the message.
 */
static void
_netlink_route_build_singlepath(
        const char *routedesc,
        int bytelen,
        struct nexthop *nexthop,
        struct nlmsghdr *nlmsg,
        struct rtmsg *rtmsg,
        size_t req_size,
	int cmd)
{
  struct nexthop_label *nh_label;
  mpls_lse_t out_lse[MPLS_MAX_LABELS];
  char label_buf[100];

  if (rtmsg->rtm_family == AF_INET &&
      (nexthop->type == NEXTHOP_TYPE_IPV6
      || nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX))
    {
      char buf[16] = "169.254.0.1";
      struct in_addr ipv4_ll;

      inet_pton (AF_INET, buf, &ipv4_ll);
      rtmsg->rtm_flags |= RTNH_F_ONLINK;
      addattr_l (nlmsg, req_size, RTA_GATEWAY, &ipv4_ll, 4);
      addattr32 (nlmsg, req_size, RTA_OIF, nexthop->ifindex);

      if (nexthop->rmap_src.ipv4.s_addr && (cmd == RTM_NEWROUTE))
        addattr_l (nlmsg, req_size, RTA_PREFSRC,
                   &nexthop->rmap_src.ipv4, bytelen);
      else if (nexthop->src.ipv4.s_addr && (cmd == RTM_NEWROUTE))
        addattr_l (nlmsg, req_size, RTA_PREFSRC,
                   &nexthop->src.ipv4, bytelen);

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug(" 5549: _netlink_route_build_singlepath() (%s): "
                   "nexthop via %s if %u",
                   routedesc, buf, nexthop->ifindex);
      return;
    }

  label_buf[0] = '\0';
  /* outgoing label - either as NEWDST (in the case of LSR) or as ENCAP
   * (in the case of LER)
   */
  nh_label = nexthop->nh_label;
  if (rtmsg->rtm_family == AF_MPLS)
    {
      assert (nh_label);
      assert (nh_label->num_labels == 1);
    }

  if (nh_label && nh_label->num_labels)
    {
      int i, num_labels = 0;
      u_int32_t bos;
      char label_buf1[20];
 
      for (i = 0; i < nh_label->num_labels; i++)
        {
          if (nh_label->label[i] != MPLS_IMP_NULL_LABEL)
            {
              bos = ((i == (nh_label->num_labels - 1)) ? 1 : 0);
              out_lse[i] = mpls_lse_encode (nh_label->label[i], 0, 0, bos);
              if (!num_labels)
                sprintf (label_buf, "label %d", nh_label->label[i]);
              else
                {
                  sprintf (label_buf1, "/%d", nh_label->label[i]);
                  strcat (label_buf, label_buf1);
                }
              num_labels++;
            }
        }
      if (num_labels)
        {
          if (rtmsg->rtm_family == AF_MPLS)
            addattr_l (nlmsg, req_size, RTA_NEWDST,
                       &out_lse, num_labels * sizeof(mpls_lse_t));
          else
            {
              struct rtattr *nest;
              u_int16_t encap = LWTUNNEL_ENCAP_MPLS;

              addattr_l(nlmsg, req_size, RTA_ENCAP_TYPE,
                        &encap, sizeof (u_int16_t));
              nest = addattr_nest(nlmsg, req_size, RTA_ENCAP);
              addattr_l (nlmsg, req_size, MPLS_IPTUNNEL_DST,
                         &out_lse, num_labels * sizeof(mpls_lse_t));
              addattr_nest_end(nlmsg, nest);
            }
        }
    }

  if (CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ONLINK))
    rtmsg->rtm_flags |= RTNH_F_ONLINK;

  if (nexthop->type == NEXTHOP_TYPE_IPV4
      || nexthop->type == NEXTHOP_TYPE_IPV4_IFINDEX)
    {
      /* Send deletes to the kernel without specifying the next-hop */
      if (cmd != RTM_DELROUTE)
        _netlink_route_nl_add_gateway_info (rtmsg->rtm_family, AF_INET, nlmsg,
                                            req_size, bytelen, nexthop);

      if (cmd == RTM_NEWROUTE)
	{
	  if (nexthop->rmap_src.ipv4.s_addr)
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->rmap_src.ipv4, bytelen);
	  else if (nexthop->src.ipv4.s_addr)
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->src.ipv4, bytelen);
	}

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via %s %s if %u",
                   routedesc,
                   inet_ntoa (nexthop->gate.ipv4),
                   label_buf, nexthop->ifindex);
    }
  if (nexthop->type == NEXTHOP_TYPE_IPV6
      || nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX)
    {
      _netlink_route_nl_add_gateway_info (rtmsg->rtm_family, AF_INET6, nlmsg,
                                          req_size, bytelen, nexthop);

      if (cmd == RTM_NEWROUTE)
	{
	  if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->rmap_src.ipv6))
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->rmap_src.ipv6, bytelen);
	  else if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->src.ipv6))
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->src.ipv6, bytelen);
	}

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via %s %s if %u",
                   routedesc,
                   inet6_ntoa (nexthop->gate.ipv6),
                   label_buf, nexthop->ifindex);
    }
  if (nexthop->type == NEXTHOP_TYPE_IFINDEX
      || nexthop->type == NEXTHOP_TYPE_IPV4_IFINDEX)
    {
      addattr32 (nlmsg, req_size, RTA_OIF, nexthop->ifindex);

      if (cmd == RTM_NEWROUTE)
	{
	  if (nexthop->rmap_src.ipv4.s_addr)
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->rmap_src.ipv4, bytelen);
	  else if (nexthop->src.ipv4.s_addr)
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->src.ipv4, bytelen);
	}

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via if %u", routedesc, nexthop->ifindex);
    }

  if (nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX)
    {
      addattr32 (nlmsg, req_size, RTA_OIF, nexthop->ifindex);

      if (cmd == RTM_NEWROUTE)
	{
	  if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->rmap_src.ipv6))
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->rmap_src.ipv6, bytelen);
	  else if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->src.ipv6))
	    addattr_l (nlmsg, req_size, RTA_PREFSRC,
		       &nexthop->src.ipv6, bytelen);
	}

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via if %u", routedesc, nexthop->ifindex);
    }
}

/* This function takes a nexthop as argument and
 * appends to the given rtattr/rtnexthop pair the
 * representation of the nexthop. If the nexthop
 * defines a preferred source, the src parameter
 * will be modified to point to that src, otherwise
 * it will be kept unmodified.
 *
 * @param routedesc: Human readable description of route type
 *                   (direct/recursive, single-/multipath)
 * @param bytelen: Length of addresses in bytes.
 * @param nexthop: Nexthop information
 * @param rta: rtnetlink attribute structure
 * @param rtnh: pointer to an rtnetlink nexthop structure
 * @param src: pointer pointing to a location where
 *             the prefsrc should be stored.
 */
static void
_netlink_route_build_multipath(
        const char *routedesc,
        int bytelen,
        struct nexthop *nexthop,
        struct rtattr *rta,
        struct rtnexthop *rtnh,
        struct rtmsg *rtmsg,
        union g_addr **src)
{
  struct nexthop_label *nh_label;
  mpls_lse_t out_lse[MPLS_MAX_LABELS];
  char label_buf[100];

  rtnh->rtnh_len = sizeof (*rtnh);
  rtnh->rtnh_flags = 0;
  rtnh->rtnh_hops = 0;
  rta->rta_len += rtnh->rtnh_len;

  if (rtmsg->rtm_family == AF_INET &&
      (nexthop->type == NEXTHOP_TYPE_IPV6
      || nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX))
    {
      char buf[16] = "169.254.0.1";
      struct in_addr ipv4_ll;

      inet_pton (AF_INET, buf, &ipv4_ll);
      bytelen = 4;
      rtnh->rtnh_flags |= RTNH_F_ONLINK;
      rta_addattr_l (rta, NL_PKT_BUF_SIZE, RTA_GATEWAY,
                     &ipv4_ll, bytelen);
      rtnh->rtnh_len += sizeof (struct rtattr) + bytelen;
      rtnh->rtnh_ifindex = nexthop->ifindex;

      if (nexthop->rmap_src.ipv4.s_addr)
        *src = &nexthop->rmap_src;
      else if (nexthop->src.ipv4.s_addr)
         *src = &nexthop->src;

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug(" 5549: netlink_route_build_multipath() (%s): "
                   "nexthop via %s if %u",
                   routedesc, buf, nexthop->ifindex);
      return;
    }

  label_buf[0] = '\0';
  /* outgoing label - either as NEWDST (in the case of LSR) or as ENCAP
   * (in the case of LER)
   */
  nh_label = nexthop->nh_label;
  if (rtmsg->rtm_family == AF_MPLS)
    {
      assert (nh_label);
      assert (nh_label->num_labels == 1);
    }

  if (nh_label && nh_label->num_labels)
    {
      int i, num_labels = 0;
      u_int32_t bos;
      char label_buf1[20];

      for (i = 0; i < nh_label->num_labels; i++)
        {
          if (nh_label->label[i] != MPLS_IMP_NULL_LABEL)
            {
              bos = ((i == (nh_label->num_labels - 1)) ? 1 : 0);
              out_lse[i] = mpls_lse_encode (nh_label->label[i], 0, 0, bos);
              if (!num_labels)
                sprintf (label_buf, "label %d", nh_label->label[i]);
              else
                {
                  sprintf (label_buf1, "/%d", nh_label->label[i]);
                  strcat (label_buf, label_buf1);
                }
              num_labels++;
            }
        }
      if (num_labels)
        {
          if (rtmsg->rtm_family == AF_MPLS)
            {
              rta_addattr_l (rta, NL_PKT_BUF_SIZE, RTA_NEWDST,
                             &out_lse, num_labels * sizeof(mpls_lse_t));
              rtnh->rtnh_len += RTA_LENGTH (num_labels * sizeof(mpls_lse_t));
            }
          else
            {
              struct rtattr *nest;
              u_int16_t encap = LWTUNNEL_ENCAP_MPLS;
              int len = rta->rta_len;

              rta_addattr_l(rta, NL_PKT_BUF_SIZE, RTA_ENCAP_TYPE,
                            &encap, sizeof (u_int16_t));
              nest = rta_nest(rta, NL_PKT_BUF_SIZE, RTA_ENCAP);
              rta_addattr_l (rta, NL_PKT_BUF_SIZE, MPLS_IPTUNNEL_DST,
                             &out_lse, num_labels * sizeof(mpls_lse_t));
              rta_nest_end(rta, nest);
              rtnh->rtnh_len += rta->rta_len - len;
            }
        }
    }

  if (CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ONLINK))
    rtnh->rtnh_flags |= RTNH_F_ONLINK;

  if (nexthop->type == NEXTHOP_TYPE_IPV4
      || nexthop->type == NEXTHOP_TYPE_IPV4_IFINDEX)
    {
      _netlink_route_rta_add_gateway_info (rtmsg->rtm_family, AF_INET, rta,
                                     rtnh, NL_PKT_BUF_SIZE, bytelen, nexthop);
      if (nexthop->rmap_src.ipv4.s_addr)
        *src = &nexthop->rmap_src;
      else if (nexthop->src.ipv4.s_addr)
         *src = &nexthop->src;

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via %s %s if %u",
                   routedesc,
                   inet_ntoa (nexthop->gate.ipv4),
                   label_buf, nexthop->ifindex);
    }
  if (nexthop->type == NEXTHOP_TYPE_IPV6
      || nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX)
    {
      _netlink_route_rta_add_gateway_info (rtmsg->rtm_family, AF_INET6, rta,
                                       rtnh, NL_PKT_BUF_SIZE, bytelen, nexthop);

      if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->rmap_src.ipv6))
        *src = &nexthop->rmap_src;
      else if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->src.ipv6))
	*src = &nexthop->src;

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via %s %s if %u",
                   routedesc,
                   inet6_ntoa (nexthop->gate.ipv6),
                   label_buf, nexthop->ifindex);
    }
  /* ifindex */
  if (nexthop->type == NEXTHOP_TYPE_IPV4_IFINDEX
      || nexthop->type == NEXTHOP_TYPE_IFINDEX)
    {
      rtnh->rtnh_ifindex = nexthop->ifindex;

      if (nexthop->rmap_src.ipv4.s_addr)
        *src = &nexthop->rmap_src;
      else if (nexthop->src.ipv4.s_addr)
        *src = &nexthop->src;

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via if %u", routedesc, nexthop->ifindex);
    }
  else if (nexthop->type == NEXTHOP_TYPE_IPV6_IFINDEX)
    {
      rtnh->rtnh_ifindex = nexthop->ifindex;

      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("netlink_route_multipath() (%s): "
                   "nexthop via if %u", routedesc, nexthop->ifindex);
    }
  else
    {
      rtnh->rtnh_ifindex = 0;
    }
}

static inline void
_netlink_mpls_build_singlepath(
        const char *routedesc,
        zebra_nhlfe_t *nhlfe,
        struct nlmsghdr *nlmsg,
        struct rtmsg *rtmsg,
        size_t req_size,
	int cmd)
{
  int bytelen;
  u_char family;

  family = NHLFE_FAMILY (nhlfe);
  bytelen = (family == AF_INET ? 4 : 16);
  _netlink_route_build_singlepath(routedesc, bytelen, nhlfe->nexthop,
                                  nlmsg, rtmsg, req_size, cmd);
}


static inline void
_netlink_mpls_build_multipath(
        const char *routedesc,
        zebra_nhlfe_t *nhlfe,
        struct rtattr *rta,
        struct rtnexthop *rtnh,
        struct rtmsg *rtmsg,
        union g_addr **src)
{
  int bytelen;
  u_char family;

  family = NHLFE_FAMILY (nhlfe);
  bytelen = (family == AF_INET ? 4 : 16);
  _netlink_route_build_multipath(routedesc, bytelen, nhlfe->nexthop,
                                 rta, rtnh, rtmsg, src);
}

/*
 * Compare if two next (first) hops are the same. We cannot use the
 * library function because there seem to be situations when a
 * next hop is of type IPV4 but actually has an 'ifindex' and in
 * such a case, we need to compare it against a next hop of type
 * IPV4_IFINDEX.
 */
static int
are_first_hops_same (struct nexthop *next1, struct nexthop *next2)
{
  switch (next1->type)
    {
    case NEXTHOP_TYPE_IPV4:
    case NEXTHOP_TYPE_IPV4_IFINDEX:
      if (next2->type != NEXTHOP_TYPE_IPV4 &&
          next2->type != NEXTHOP_TYPE_IPV4_IFINDEX)
	return 0;
      if (! IPV4_ADDR_SAME (&next1->gate.ipv4, &next2->gate.ipv4))
	return 0;
      if (next1->ifindex != next2->ifindex)
	return 0;
      break;
    case NEXTHOP_TYPE_IFINDEX:
      if (next1->type != next2->type)
        return 0;
      if (next1->ifindex != next2->ifindex)
	return 0;
      break;
    case NEXTHOP_TYPE_IPV6:
    case NEXTHOP_TYPE_IPV6_IFINDEX:
      if (next2->type != NEXTHOP_TYPE_IPV6 &&
          next2->type != NEXTHOP_TYPE_IPV6_IFINDEX)
	return 0;
      if (! IPV6_ADDR_SAME (&next1->gate.ipv6, &next2->gate.ipv6))
	return 0;
      if (next1->ifindex != next2->ifindex)
	return 0;
      break;
    default:
      /* do nothing */
      break;
    }
  return 1;
}

/*
 * While forming RTA_MULTIPATH, weed out any duplicate next hop.
 */
static int
is_duplicate_first_hop (struct nexthop *nexthop, struct nexthop **nhops,
                        int nhop_num)
{
  int i;
  char buf[PREFIX_STRLEN];
  char buf2[PREFIX_STRLEN];

  for (i = 0; i < nhop_num; i++)
    {
      /* TODO: To be removed after tests. */
      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug("Comparing Nexthop %s to existing %s [%d]",
                   nexthop2str (nexthop, buf, sizeof(buf)),
                   nexthop2str (nhops[i], buf2, sizeof(buf2)), i);
      if (are_first_hops_same (nexthop, nhops[i]))
        return 1;
    }

  /* NOTE: As a side effect, we also update the 'nhops' array. */
  nhops[nhop_num] = nexthop;
  return 0;
}

/* Log debug information for netlink_route_multipath
 * if debug logging is enabled.
 *
 * @param cmd: Netlink command which is to be processed
 * @param p: Prefix for which the change is due
 * @param nexthop: Nexthop which is currently processed
 * @param routedesc: Semantic annotation for nexthop
 *                     (recursive, multipath, etc.)
 * @param family: Address family which the change concerns
 */
static void
_netlink_route_debug(
        int cmd,
        struct prefix *p,
        struct nexthop *nexthop,
        const char *routedesc,
        int family,
        struct zebra_vrf *zvrf)
{
  if (IS_ZEBRA_DEBUG_KERNEL)
    {
      char buf[PREFIX_STRLEN];
      zlog_debug ("netlink_route_multipath() (%s): %s %s vrf %u type %s",
		  routedesc,
		  nl_msg_type_to_str (cmd),
		  prefix2str (p, buf, sizeof(buf)), zvrf->vrf_id,
		  (nexthop) ? nexthop_type_to_str (nexthop->type) : "UNK");
    }
}

static void
_netlink_mpls_debug(
        int cmd,
        u_int32_t label,
        const char *routedesc)
{
  if (IS_ZEBRA_DEBUG_KERNEL)
    zlog_debug ("netlink_mpls_multipath() (%s): %s %u/20",
                routedesc, nl_msg_type_to_str (cmd), label);
}

static int
netlink_neigh_update (int cmd, int ifindex, uint32_t addr, char *lla, int llalen)
{
  struct {
      struct nlmsghdr         n;
      struct ndmsg            ndm;
      char                    buf[256];
  } req;

  struct zebra_ns *zns = zebra_ns_lookup (NS_DEFAULT);

  memset(&req.n, 0, sizeof(req.n));
  memset(&req.ndm, 0, sizeof(req.ndm));

  req.n.nlmsg_len = NLMSG_LENGTH(sizeof(struct ndmsg));
  req.n.nlmsg_flags = NLM_F_CREATE | NLM_F_REQUEST;
  req.n.nlmsg_type = cmd; //RTM_NEWNEIGH or RTM_DELNEIGH
  req.ndm.ndm_family = AF_INET;
  req.ndm.ndm_state = NUD_PERMANENT;
  req.ndm.ndm_ifindex = ifindex;
  req.ndm.ndm_type = RTN_UNICAST;

  addattr_l(&req.n, sizeof(req), NDA_DST, &addr, 4);
  addattr_l(&req.n, sizeof(req), NDA_LLADDR, lla, llalen);

  return netlink_talk (netlink_talk_filter, &req.n, &zns->netlink_cmd, zns);
}

static int
netlink_neigh_update_af_bridge (struct interface *ifp, vlanid_t vid,
                                struct ethaddr *mac, struct in_addr vtep_ip,
                                int cmd)
{
  struct zebra_ns *zns = zebra_ns_lookup (NS_DEFAULT);
  struct
    {
      struct nlmsghdr         n;
      struct ndmsg            ndm;
      char                    buf[256];
    } req;
  int dst_alen;
  struct zebra_if *zif;
  struct zebra_l2info_brslave *br_slave;
  struct interface *br_if;
  struct zebra_if *br_zif;
  char buf[MACADDR_STRLEN];

  zif = ifp->info;
  br_slave = (struct zebra_l2info_brslave *)zif->l2if;
  if ((br_if = br_slave->br_if) == NULL)
    {
      zlog_warn ("MAC %s on IF %s(%u) - no mapping to bridge",
                 (cmd == RTM_NEWNEIGH) ? "add" : "del",
                 ifp->name, ifp->ifindex);
      return -1;
    }

  memset(&req.n, 0, sizeof(req.n));
  memset(&req.ndm, 0, sizeof(req.ndm));

  req.n.nlmsg_len = NLMSG_LENGTH(sizeof(struct ndmsg));
  req.n.nlmsg_flags = NLM_F_REQUEST;
  if (cmd == RTM_NEWNEIGH)
    req.n.nlmsg_flags |= (NLM_F_CREATE | NLM_F_REPLACE);
  req.n.nlmsg_type = cmd;
  req.ndm.ndm_family = AF_BRIDGE;
  req.ndm.ndm_state = NUD_REACHABLE;
  req.ndm.ndm_flags |= NTF_SELF | NTF_MASTER;

  addattr_l (&req.n, sizeof (req), NDA_LLADDR, mac, 6);
  req.ndm.ndm_ifindex = ifp->ifindex;
  dst_alen = 4; // TODO: hardcoded
  addattr_l (&req.n, sizeof (req), NDA_DST, &vtep_ip, dst_alen);
  br_zif = (struct zebra_if *) br_if->info;
  if (IS_ZEBRA_IF_BRIDGE_VLAN_AWARE(br_zif) && vid > 0)
    addattr16 (&req.n, sizeof (req), NDA_VLAN, vid);
  addattr32 (&req.n, sizeof (req), NDA_MASTER, br_if->ifindex);

  if (IS_ZEBRA_DEBUG_KERNEL)
    zlog_debug ("Tx %s family %s IF %s(%u) vlan %d MAC %s Remote VTEP %s",
                nl_msg_type_to_str (cmd),
                nl_family_to_str (req.ndm.ndm_family),
                ifp->name, ifp->ifindex, vid,
                mac2str (mac, buf, sizeof (buf)),
                inet_ntoa (vtep_ip));

  return netlink_talk (netlink_talk_filter, &req.n, &zns->netlink_cmd, zns);
}

/* Routing table change via netlink interface. */
/* Update flag indicates whether this is a "replace" or not. */
static int
netlink_route_multipath (int cmd, struct prefix *p, struct rib *rib,
                         int update)
{
  int bytelen;
  struct sockaddr_nl snl;
  struct nexthop *nexthop = NULL, *tnexthop;
  int recursing;
  unsigned int nexthop_num;
  int discard;
  int family = PREFIX_FAMILY(p);
  const char *routedesc;
  int setsrc = 0;
  union g_addr src;

  struct
  {
    struct nlmsghdr n;
    struct rtmsg r;
    char buf[NL_PKT_BUF_SIZE];
  } req;

  struct zebra_ns *zns = zebra_ns_lookup (NS_DEFAULT);
  struct zebra_vrf *zvrf = vrf_info_lookup (rib->vrf_id);

  memset (&req, 0, sizeof req - NL_PKT_BUF_SIZE);

  bytelen = (family == AF_INET ? 4 : 16);

  req.n.nlmsg_len = NLMSG_LENGTH (sizeof (struct rtmsg));
  req.n.nlmsg_flags = NLM_F_CREATE | NLM_F_REQUEST;
  if ((cmd == RTM_NEWROUTE) && update)
    req.n.nlmsg_flags |= NLM_F_REPLACE;
  req.n.nlmsg_type = cmd;
  req.r.rtm_family = family;
  req.r.rtm_dst_len = p->prefixlen;
  req.r.rtm_protocol = get_rt_proto(rib->type);
  req.r.rtm_scope = RT_SCOPE_UNIVERSE;

  if ((rib->flags & ZEBRA_FLAG_BLACKHOLE) || (rib->flags & ZEBRA_FLAG_REJECT))
    discard = 1;
  else
    discard = 0;

  if (cmd == RTM_NEWROUTE)
    {
      if (discard)
        {
          if (rib->flags & ZEBRA_FLAG_BLACKHOLE)
            req.r.rtm_type = RTN_BLACKHOLE;
          else if (rib->flags & ZEBRA_FLAG_REJECT)
            req.r.rtm_type = RTN_UNREACHABLE;
          else
            assert (RTN_BLACKHOLE != RTN_UNREACHABLE);  /* false */
        }
      else
        req.r.rtm_type = RTN_UNICAST;
    }

  addattr_l (&req.n, sizeof req, RTA_DST, &p->u.prefix, bytelen);

  /* Metric. */
  /* Hardcode the metric for all routes coming from zebra. Metric isn't used
   * either by the kernel or by zebra. Its purely for calculating best path(s)
   * by the routing protocol and for communicating with protocol peers.
   */
  addattr32 (&req.n, sizeof req, RTA_PRIORITY, NL_DEFAULT_ROUTE_METRIC);

  /* Table corresponding to this route. */
  if (rib->table < 256)
    req.r.rtm_table = rib->table;
  else
    {
      req.r.rtm_table = RT_TABLE_UNSPEC;
      addattr32(&req.n, sizeof req, RTA_TABLE, rib->table);
    }

  if (rib->mtu || rib->nexthop_mtu)
    {
      char buf[NL_PKT_BUF_SIZE];
      struct rtattr *rta = (void *) buf;
      u_int32_t mtu = rib->mtu;
      if (!mtu || (rib->nexthop_mtu && rib->nexthop_mtu < mtu))
        mtu = rib->nexthop_mtu;
      rta->rta_type = RTA_METRICS;
      rta->rta_len = RTA_LENGTH(0);
      rta_addattr_l (rta, NL_PKT_BUF_SIZE, RTAX_MTU, &mtu, sizeof mtu);
      addattr_l (&req.n, NL_PKT_BUF_SIZE, RTA_METRICS, RTA_DATA (rta),
                 RTA_PAYLOAD (rta));
    }

  if (discard)
    {
      if (cmd == RTM_NEWROUTE)
        for (ALL_NEXTHOPS_RO(rib->nexthop, nexthop, tnexthop, recursing))
          {
            /* We shouldn't encounter recursive nexthops on discard routes,
             * but it is probably better to handle that case correctly anyway.
             */
            if (CHECK_FLAG(nexthop->flags, NEXTHOP_FLAG_RECURSIVE))
              continue;
          }
      goto skip;
    }

  /* Count overall nexthops so we can decide whether to use singlepath
   * or multipath case. */
  nexthop_num = 0;
  for (ALL_NEXTHOPS_RO(rib->nexthop, nexthop, tnexthop, recursing))
    {
      if (CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_RECURSIVE))
        continue;
      if (cmd == RTM_NEWROUTE && !CHECK_FLAG(nexthop->flags, NEXTHOP_FLAG_ACTIVE))
        continue;
      if (cmd == RTM_DELROUTE && !CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB))
        continue;

      nexthop_num++;
    }

  /* Singlepath case. */
  if (nexthop_num == 1 || multipath_num == 1)
    {
      nexthop_num = 0;
      for (ALL_NEXTHOPS_RO(rib->nexthop, nexthop, tnexthop, recursing))
        {
          if (CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_RECURSIVE))
            {
              if (!setsrc)
                 {
		   if (family == AF_INET)
		     {
		       if (nexthop->rmap_src.ipv4.s_addr != 0)
			 {
			   src.ipv4 = nexthop->rmap_src.ipv4;
			   setsrc = 1;
			 }
		       else if (nexthop->src.ipv4.s_addr != 0)
			 {
			   src.ipv4 = nexthop->src.ipv4;
			   setsrc = 1;
			 }
		     }
		   else if (family == AF_INET6)
		     {
		       if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->rmap_src.ipv6))
			 {
			   src.ipv6 = nexthop->rmap_src.ipv6;
			   setsrc = 1;
			 }
		       else if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->src.ipv6))
			 {
			   src.ipv6 = nexthop->src.ipv6;
			   setsrc = 1;
			 }
		     }
                 }
              continue;
	    }

          if ((cmd == RTM_NEWROUTE
               && CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ACTIVE))
              || (cmd == RTM_DELROUTE
                  && CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB)))
            {
              routedesc = recursing ? "recursive, 1 hop" : "single hop";

              _netlink_route_debug(cmd, p, nexthop, routedesc, family, zvrf);
              _netlink_route_build_singlepath(routedesc, bytelen,
                                              nexthop, &req.n, &req.r,
                                              sizeof req, cmd);
              nexthop_num++;
              break;
            }
        }
      if (setsrc && (cmd == RTM_NEWROUTE))
	{
	  if (family == AF_INET)
	    addattr_l (&req.n, sizeof req, RTA_PREFSRC, &src.ipv4, bytelen);
	  else if (family == AF_INET6)
	    addattr_l (&req.n, sizeof req, RTA_PREFSRC, &src.ipv6, bytelen);
	}
    }
  else
    {
      char buf[NL_PKT_BUF_SIZE];
      struct rtattr *rta = (void *) buf;
      struct rtnexthop *rtnh;
      union g_addr *src1 = NULL;
      struct nexthop *nhops[MULTIPATH_NUM];

      rta->rta_type = RTA_MULTIPATH;
      rta->rta_len = RTA_LENGTH (0);
      rtnh = RTA_DATA (rta);

      nexthop_num = 0;
      memset (nhops, 0, sizeof (nhops));
      for (ALL_NEXTHOPS_RO(rib->nexthop, nexthop, tnexthop, recursing))
        {
          if (nexthop_num >= multipath_num)
            break;

          if (CHECK_FLAG(nexthop->flags, NEXTHOP_FLAG_RECURSIVE))
	    {
              /* This only works for IPv4 now */
              if (!setsrc)
                 {
		   if (family == AF_INET)
		     {
		       if (nexthop->rmap_src.ipv4.s_addr != 0)
			 {
			   src.ipv4 = nexthop->rmap_src.ipv4;
			   setsrc = 1;
			 }
		       else if (nexthop->src.ipv4.s_addr != 0)
			 {
			   src.ipv4 = nexthop->src.ipv4;
			   setsrc = 1;
			 }
		     }
		   else if (family == AF_INET6)
		     {
		       if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->rmap_src.ipv6))
			 {
			   src.ipv6 = nexthop->rmap_src.ipv6;
			   setsrc = 1;
			 }
		       else if (!IN6_IS_ADDR_UNSPECIFIED(&nexthop->src.ipv6))
			 {
			   src.ipv6 = nexthop->src.ipv6;
			   setsrc = 1;
			 }
		     }
                 }
	      continue;
	    }

          if ((cmd == RTM_NEWROUTE
               && CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ACTIVE)
               && !is_duplicate_first_hop (nexthop, nhops, nexthop_num))
              || (cmd == RTM_DELROUTE
                  && CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB)))
            {
              routedesc = recursing ? "recursive, multihop" : "multihop";
              nexthop_num++;

              _netlink_route_debug(cmd, p, nexthop,
                                   routedesc, family, zvrf);
              _netlink_route_build_multipath(routedesc, bytelen,
                                             nexthop, rta, rtnh, &req.r, &src1);
              rtnh = RTNH_NEXT (rtnh);

	      if (!setsrc && src1)
		{
		  if (family == AF_INET)
		    src.ipv4 = src1->ipv4;
		  else if (family == AF_INET6)
		    src.ipv6 = src1->ipv6;

		  setsrc = 1;
		}
            }
        }
      if (setsrc && (cmd == RTM_NEWROUTE))
	{
	  if (family == AF_INET)
	    addattr_l (&req.n, sizeof req, RTA_PREFSRC, &src.ipv4, bytelen);
	  else if (family == AF_INET6)
	    addattr_l (&req.n, sizeof req, RTA_PREFSRC, &src.ipv6, bytelen);
          if (IS_ZEBRA_DEBUG_KERNEL)
	    zlog_debug("Setting source");
	}

      if (rta->rta_len > RTA_LENGTH (0))
        addattr_l (&req.n, NL_PKT_BUF_SIZE, RTA_MULTIPATH, RTA_DATA (rta),
                   RTA_PAYLOAD (rta));
    }

  /* If there is no useful nexthop then return. */
  if (nexthop_num == 0)
    {
      if (IS_ZEBRA_DEBUG_KERNEL)
        zlog_debug ("netlink_route_multipath(): No useful nexthop.");
      return 0;
    }

skip:

  /* Destination netlink address. */
  memset (&snl, 0, sizeof snl);
  snl.nl_family = AF_NETLINK;

  /* Talk to netlink socket. */
  return netlink_talk (netlink_talk_filter, &req.n, &zns->netlink_cmd, zns);
}

int
netlink_get_ipmr_sg_stats (void *in)
{
  int suc = 0;
  struct mcast_route_data *mr = (struct mcast_route_data *)in;
  struct {
      struct nlmsghdr         n;
      struct ndmsg            ndm;
      char                    buf[256];
  } req;

  mroute = mr;
  struct zebra_ns *zns = zebra_ns_lookup (NS_DEFAULT);

  memset(&req.n, 0, sizeof(req.n));
  memset(&req.ndm, 0, sizeof(req.ndm));

  req.n.nlmsg_len = NLMSG_LENGTH(sizeof(struct ndmsg));
  req.n.nlmsg_flags = NLM_F_REQUEST;
  req.ndm.ndm_family = AF_INET;
  req.n.nlmsg_type = RTM_GETROUTE;

  addattr_l (&req.n, sizeof (req), RTA_IIF, &mroute->ifindex, 4);
  addattr_l (&req.n, sizeof (req), RTA_OIF, &mroute->ifindex, 4);
  addattr_l (&req.n, sizeof (req), RTA_SRC, &mroute->sg.src.s_addr, 4);
  addattr_l (&req.n, sizeof (req), RTA_DST, &mroute->sg.grp.s_addr, 4);

  suc = netlink_talk (netlink_route_change_read_multicast, &req.n, &zns->netlink_cmd, zns);

  mroute = NULL;
  return suc;
}

int
kernel_route_rib (struct prefix *p, struct rib *old, struct rib *new)
{
  if (!old && new)
    return netlink_route_multipath (RTM_NEWROUTE, p, new, 0);
  if (old && !new)
    return netlink_route_multipath (RTM_DELROUTE, p, old, 0);

  return netlink_route_multipath (RTM_NEWROUTE, p, new, 1);
}

int
kernel_neigh_update (int add, int ifindex, uint32_t addr, char *lla, int llalen)
{
  return netlink_neigh_update(add ? RTM_NEWNEIGH : RTM_DELNEIGH, ifindex, addr,
			      lla, llalen);
}

int
kernel_add_mac (struct interface *ifp, vlanid_t vid,
                struct ethaddr *mac, struct in_addr vtep_ip)
{
 return netlink_neigh_update_af_bridge (ifp, vid, mac, vtep_ip,
                                        RTM_NEWNEIGH);
}

int
kernel_del_mac (struct interface *ifp, vlanid_t vid,
                struct ethaddr *mac, struct in_addr vtep_ip)
{
 return netlink_neigh_update_af_bridge (ifp, vid, mac, vtep_ip,
                                        RTM_DELNEIGH);
}

/*
 * MPLS label forwarding table change via netlink interface.
 */
int
netlink_mpls_multipath (int cmd, zebra_lsp_t *lsp)
{
  mpls_lse_t lse;
  zebra_nhlfe_t *nhlfe;
  struct nexthop *nexthop = NULL;
  unsigned int nexthop_num;
  const char *routedesc;
  struct zebra_ns *zns = zebra_ns_lookup (NS_DEFAULT);

  struct
  {
    struct nlmsghdr n;
    struct rtmsg r;
    char buf[NL_PKT_BUF_SIZE];
  } req;

  memset (&req, 0, sizeof req - NL_PKT_BUF_SIZE);


  /*
   * Count # nexthops so we can decide whether to use singlepath
   * or multipath case.
   */
  nexthop_num = 0;
  for (nhlfe = lsp->nhlfe_list; nhlfe; nhlfe = nhlfe->next)
    {
      nexthop = nhlfe->nexthop;
      if (!nexthop)
        continue;
      if (cmd == RTM_NEWROUTE)
        {
          /* Count all selected NHLFEs */
          if (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_SELECTED) &&
              CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ACTIVE))
            nexthop_num++;
        }
      else /* DEL */
        {
          /* Count all installed NHLFEs */
          if (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED) &&
              CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB))
            nexthop_num++;
        }
    }

  if (nexthop_num == 0) // unexpected
    return 0;

  req.n.nlmsg_len = NLMSG_LENGTH (sizeof (struct rtmsg));
  req.n.nlmsg_flags = NLM_F_CREATE | NLM_F_REQUEST;
  req.n.nlmsg_type = cmd;
  req.r.rtm_family = AF_MPLS;
  req.r.rtm_table = RT_TABLE_MAIN;
  req.r.rtm_dst_len = MPLS_LABEL_LEN_BITS;
  req.r.rtm_protocol = RTPROT_ZEBRA;
  req.r.rtm_scope = RT_SCOPE_UNIVERSE;
  req.r.rtm_type = RTN_UNICAST;

  if (cmd == RTM_NEWROUTE)
    /* We do a replace to handle update. */
    req.n.nlmsg_flags |= NLM_F_REPLACE;

  /* Fill destination */
  lse = mpls_lse_encode (lsp->ile.in_label, 0, 0, 1);
  addattr_l (&req.n, sizeof req, RTA_DST, &lse, sizeof(mpls_lse_t));

  /* Fill nexthops (paths) based on single-path or multipath. The paths
   * chosen depend on the operation.
   */
  if (nexthop_num == 1 || multipath_num == 1)
    {
      routedesc = "single hop";
      _netlink_mpls_debug(cmd, lsp->ile.in_label, routedesc);

      nexthop_num = 0;
      for (nhlfe = lsp->nhlfe_list; nhlfe; nhlfe = nhlfe->next)
        {
          nexthop = nhlfe->nexthop;
          if (!nexthop)
            continue;

          if ((cmd == RTM_NEWROUTE &&
               (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_SELECTED) &&
                CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ACTIVE))) ||
              (cmd == RTM_DELROUTE &&
               (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED) &&
                CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB))))
            {
              /* Add the gateway */
              _netlink_mpls_build_singlepath(routedesc, nhlfe,
                                             &req.n, &req.r, sizeof req, cmd);
              if (cmd == RTM_NEWROUTE)
                {
                  SET_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED);
                  SET_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB);
                }
              else
                {
                  UNSET_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED);
                  UNSET_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB);
                }
              nexthop_num++;
              break;
            }
        }
    }
  else /* Multipath case */
    {
      char buf[NL_PKT_BUF_SIZE];
      struct rtattr *rta = (void *) buf;
      struct rtnexthop *rtnh;
      union g_addr *src1 = NULL;

      rta->rta_type = RTA_MULTIPATH;
      rta->rta_len = RTA_LENGTH (0);
      rtnh = RTA_DATA (rta);

      routedesc = "multihop";
      _netlink_mpls_debug(cmd, lsp->ile.in_label, routedesc);

      nexthop_num = 0;
      for (nhlfe = lsp->nhlfe_list; nhlfe; nhlfe = nhlfe->next)
        {
          nexthop = nhlfe->nexthop;
          if (!nexthop)
            continue;

          if (nexthop_num >= multipath_num)
            break;

          if ((cmd == RTM_NEWROUTE &&
               (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_SELECTED) &&
                CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_ACTIVE))) ||
              (cmd == RTM_DELROUTE &&
               (CHECK_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED) &&
                CHECK_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB))))
            {
              nexthop_num++;

              /* Build the multipath */
              _netlink_mpls_build_multipath(routedesc, nhlfe, rta,
                                            rtnh, &req.r, &src1);
              rtnh = RTNH_NEXT (rtnh);

              if (cmd == RTM_NEWROUTE)
                {
                  SET_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED);
                  SET_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB);
                }
              else
                {
                  UNSET_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED);
                  UNSET_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB);
                }

            }
        }

      /* Add the multipath */
      if (rta->rta_len > RTA_LENGTH (0))
        addattr_l (&req.n, NL_PKT_BUF_SIZE, RTA_MULTIPATH, RTA_DATA (rta),
                   RTA_PAYLOAD (rta));
    }

  /* Talk to netlink socket. */
  return netlink_talk (netlink_talk_filter, &req.n, &zns->netlink_cmd, zns);
}

/*
 * Handle failure in LSP install, clear flags for NHLFE.
 */
void
clear_nhlfe_installed (zebra_lsp_t *lsp)
{
  zebra_nhlfe_t *nhlfe;
  struct nexthop *nexthop;

  for (nhlfe = lsp->nhlfe_list; nhlfe; nhlfe = nhlfe->next)
    {
      nexthop = nhlfe->nexthop;
      if (!nexthop)
        continue;

      UNSET_FLAG (nhlfe->flags, NHLFE_FLAG_INSTALLED);
      UNSET_FLAG (nexthop->flags, NEXTHOP_FLAG_FIB);
    }
}
