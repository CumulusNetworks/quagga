#include <zebra.h>
#include "zebra/rib.h"
#include "zebra/zserv.h"
#include "zebra/zebra_rnh.h"

int zebra_rnh_ip_default_route = 0;
int zebra_rnh_ipv6_default_route = 0;

int zebra_evaluate_rnh_table (int vrfid, int family)
{ return 0; }

void zebra_print_rnh_table (int vrfid, int family, struct vty *vty)
{}
