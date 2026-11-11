#ifndef SM2_TABLE_H
#define SM2_TABLE_H

#include "ecc.h"

/* Verification interface for the fixed tables defined by the source
 * sm2_table.h.  The table literals and their checked mathematical model live
 * in the imported Rocq library. */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table
 */

/*@ Extern Coq
      (SM2_G_POINT : ec_point)
      (store_sm2_base_point_table : Assertion)
      (store_sm2_mont_base_point_table : Assertion)
 */

#endif
