#ifndef BASEPOINT_TRACE_H
#define BASEPOINT_TRACE_H

#include "sm2_table.h"

extern const AFPoint g_AFTable_for_base_point_mul[4][8][256];
extern const AFPoint g_montg_AFTable_for_base_point_mul[4][8][256];

/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul
 */

/*@ Extern Coq (RecordAFPoint :: *) */
/*@ Extern Coq
      (SM2_BYTE_BASE : Z)
      (SM2_BASE_TABLE_DATA : list (list RecordAFPoint))
      (SM2_MONT_BASE_TABLE_DATA : list (list RecordAFPoint))
      (SM2_TABLE_RECORDS : Z)
      (sm2_base_table_correct : list (list RecordAFPoint) -> Prop)
      (sm2_mont_base_table_correct : Prop)
      (sm2_table_flatten : list (list RecordAFPoint) -> list RecordAFPoint)
      (sm2_base_table_flat_index : Z -> Z -> Z -> Z)
      (sm2_base_table_record_at : Z -> Z -> Z -> RecordAFPoint)
      (sm2_mont_base_table_record_at : Z -> Z -> Z -> RecordAFPoint)
      (sm2_scalar_prefix : Z -> Z -> Z)
      (sm2_scalar_chunk : Z -> Z -> Z -> Z)
      (sm2_scalar_term : Z -> Z -> Z -> Z)
      (sm2_table_term : Z -> Z -> Z -> Z)
      (record_afpoint_well_formed : RecordAFPoint -> Prop)
      (u8_list_value : list Z -> Z)
      (u8_list_bounded : list Z -> Prop)
      (aligned_4 : Z -> Prop)
 */

#endif
