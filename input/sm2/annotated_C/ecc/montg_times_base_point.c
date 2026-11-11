/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_times_base_point. */

#include "../include/ecc.h"
#include "../include/sm2_table.h"
#include "../include/basepoint_trace.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/basepoint_bytes.strategies" */
/*@ include strategies "../strategy/basepoint_table_points.strategies" */
/*@ Import Coq Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_basepoint_mul
 */

typedef unsigned char uint8_t;
#define NULL 0

extern const AFPoint g_montg_AFTable_for_base_point_mul[4][8][256];

int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ point_non_alias
    With (P : ec_point)
    Require
      store_mont_afpoint(point, P) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero * store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(point, P) *
      store_mont_jpoint(result, P) *
      store_bn_zero * store_montg_one
 */;

void montg_add_jpoint_and_apoint_ex(
    const JPoint* a, const AFPoint* b, JPoint* result)
/*@ r_eq_a
    With (P1 P2 : ec_point)
    Require
      result == a &&
      store_mont_jpoint(a, P1) *
      store_mont_afpoint(b, P2) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == a &&
      store_mont_jpoint(result, sm2_point_add(P1, P2)) *
      store_mont_afpoint(b, P2) *
      store_bn_zero * store_montg_one *
      store_sm2_p * store_sm2_rhop
 */;

void montg_add_jpoint_ex(
    const JPoint* a, const JPoint* b, JPoint* result)
/*@ r_eq_a
    With (P1 P2 : ec_point)
    Require
      result == a &&
      store_mont_jpoint(a, P1) *
      store_mont_jpoint(b, P2) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      result == a &&
      store_mont_jpoint(result, sm2_point_add(P1, P2)) *
      store_mont_jpoint(b, P2) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */
/*@ non_alias
    With (P1 P2 : ec_point)
    Require
      store_mont_jpoint(a, P1) *
      store_mont_jpoint(b, P2) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
    Ensure
      store_mont_jpoint(a, P1) *
      store_mont_jpoint(b, P2) *
      store_mont_jpoint(result, sm2_point_add(P1, P2)) *
      store_bn_zero * store_sm2_p * store_sm2_rhop
 */;

void montg_times_base_point(const u32* k, JPoint* result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_mont_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
    Ensure
      store_fn(k, K) *
      store_mont_jpoint(result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_mont_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
 */
{
	int i = 0;
	uint8_t byteIdx = 0;
	uint8_t* pk = NULL;
	const AFPoint *pT = NULL;
	JPoint K0, K1, K2, K3;

	/*@
	  store_fn(k, K)
	  which implies
	  exists byte_list,
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    UCharArray::full(&(k->v[0]), 32, byte_list)
	 */
	/*@ Given byte_list */
	/*@ do basepoint_bytes_split32 */
	/*@
	  store_sm2_mont_base_point_table
	  which implies
	  sm2_mont_base_table_correct &&
	  StructAFPointArray::full(
	    &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	    sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA))
	 */

	// k[0]
	pk = (uint8_t*)(k->v + 0);
	/*@ do basepoint_bytes_alias_to_local */
	byteIdx = pk[0];
	/*@
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  Zlength(byte_list) == 32 &&
	  u8_list_bounded(byte_list) &&
	  byteIdx == sublist(0, 8, byte_list)[0]
	  which implies
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  0 <= byteIdx && byteIdx < 256
	 */
	pT = &(g_montg_AFTable_for_base_point_mul[0][0][byteIdx]);
	montg_apoint_to_jpoint2(pT, &K0)
	/*@ where (point_non_alias)
	      P = sm2_point_mul(sm2_table_term(byteIdx, 0, 0), SM2_G_POINT)
	 */;
	/*@ Inv Assert
	  exists PT B,
	    k == k@pre && result == result@pre &&
	    pk == &(k->v[0]) && pT == PT && byteIdx == B &&
	    1 <= i && i <= 8 &&
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    sm2_mont_base_table_correct &&
	    UCharArray::full(pk, 8, sublist(0, 8, byte_list)) *
	    UCharArray::full(&(k->v[1]), 8, sublist(8, 16, byte_list)) *
	    UCharArray::full(&(k->v[2]), 8, sublist(16, 24, byte_list)) *
	    UCharArray::full(&(k->v[3]), 8, sublist(24, 32, byte_list)) *
	    store_mont_jpoint(
	      &K0, sm2_point_mul(sm2_scalar_chunk(K, 0, i), SM2_G_POINT)) *
	    UInt64Array::undef_full(&(K1.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K1.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K1.z.v[0]), 4) *
	    UInt64Array::undef_full(&(K2.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K2.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K2.z.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.z.v[0]), 4) *
	    UInt64Array::undef_full(&(result->x.v[0]), 4) *
	    UInt64Array::undef_full(&(result->y.v[0]), 4) *
	    UInt64Array::undef_full(&(result->z.v[0]), 4) *
	    StructAFPointArray::full(
	      &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	      sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA)) *
	    store_sm2_p * store_sm2_rhop *
	    store_bn_zero * store_montg_one
	 */
	for (i = 1; i < 8; i++)
	{
		/*@ Given PT B */
		byteIdx = pk[i];
		/*@
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  Zlength(byte_list) == 32 &&
		  u8_list_bounded(byte_list) && 1 <= i && i < 8 &&
		  byteIdx == sublist(0, 8, byte_list)[i]
		  which implies
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  0 <= byteIdx && byteIdx < 256
		 */
		pT = &(g_montg_AFTable_for_base_point_mul[0][i][byteIdx]);
		montg_add_jpoint_and_apoint_ex(&K0, pT, &K0)
		/*@ where (r_eq_a)
		      P1 = sm2_point_mul(sm2_scalar_chunk(K, 0, i), SM2_G_POINT),
		      P2 = sm2_point_mul(sm2_table_term(byteIdx, 0, i), SM2_G_POINT)
		 */;
	}
	/*@ do basepoint_bytes_alias_to_canonical */
	// k[1]
	pk = (uint8_t*)(k->v + 1);
	/*@ do basepoint_bytes_alias_to_local */
	byteIdx = pk[0];
	/*@
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  Zlength(byte_list) == 32 &&
	  u8_list_bounded(byte_list) &&
	  byteIdx == sublist(8, 16, byte_list)[0]
	  which implies
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  0 <= byteIdx && byteIdx < 256
	 */
	pT = &(g_montg_AFTable_for_base_point_mul[1][0][byteIdx]);
	montg_apoint_to_jpoint2(pT, &K1)
	/*@ where (point_non_alias)
	      P = sm2_point_mul(sm2_table_term(byteIdx, 1, 0), SM2_G_POINT)
	 */;
	/*@ Inv Assert
	  exists PT B,
	    k == k@pre && result == result@pre &&
	    pk == &(k->v[1]) && pT == PT && byteIdx == B &&
	    1 <= i && i <= 8 &&
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    sm2_mont_base_table_correct &&
	    UCharArray::full(&(k->v[0]), 8, sublist(0, 8, byte_list)) *
	    UCharArray::full(pk, 8, sublist(8, 16, byte_list)) *
	    UCharArray::full(&(k->v[2]), 8, sublist(16, 24, byte_list)) *
	    UCharArray::full(&(k->v[3]), 8, sublist(24, 32, byte_list)) *
	    store_mont_jpoint(
	      &K0, sm2_point_mul(sm2_scalar_chunk(K, 0, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K1, sm2_point_mul(sm2_scalar_chunk(K, 1, i), SM2_G_POINT)) *
	    UInt64Array::undef_full(&(K2.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K2.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K2.z.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.z.v[0]), 4) *
	    UInt64Array::undef_full(&(result->x.v[0]), 4) *
	    UInt64Array::undef_full(&(result->y.v[0]), 4) *
	    UInt64Array::undef_full(&(result->z.v[0]), 4) *
	    StructAFPointArray::full(
	      &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	      sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA)) *
	    store_sm2_p * store_sm2_rhop *
	    store_bn_zero * store_montg_one
	 */
	for (i = 1; i < 8; i++)
	{
		/*@ Given PT B */
		byteIdx = pk[i];
		/*@
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  Zlength(byte_list) == 32 &&
		  u8_list_bounded(byte_list) && 1 <= i && i < 8 &&
		  byteIdx == sublist(8, 16, byte_list)[i]
		  which implies
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  0 <= byteIdx && byteIdx < 256
		 */
		pT = &(g_montg_AFTable_for_base_point_mul[1][i][byteIdx]);
		montg_add_jpoint_and_apoint_ex(&K1, pT, &K1)
		/*@ where (r_eq_a)
		      P1 = sm2_point_mul(sm2_scalar_chunk(K, 1, i), SM2_G_POINT),
		      P2 = sm2_point_mul(sm2_table_term(byteIdx, 1, i), SM2_G_POINT)
		 */;
	}
	/*@ do basepoint_bytes_alias_to_canonical */
	// k[2]
	pk = (uint8_t*)(k->v + 2);
	/*@ do basepoint_bytes_alias_to_local */
	byteIdx = pk[0];
	/*@
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  Zlength(byte_list) == 32 &&
	  u8_list_bounded(byte_list) &&
	  byteIdx == sublist(16, 24, byte_list)[0]
	  which implies
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  0 <= byteIdx && byteIdx < 256
	 */
	pT = &(g_montg_AFTable_for_base_point_mul[2][0][byteIdx]);
	montg_apoint_to_jpoint2(pT, &K2)
	/*@ where (point_non_alias)
	      P = sm2_point_mul(sm2_table_term(byteIdx, 2, 0), SM2_G_POINT)
	 */;
	/*@ Inv Assert
	  exists PT B,
	    k == k@pre && result == result@pre &&
	    pk == &(k->v[2]) && pT == PT && byteIdx == B &&
	    1 <= i && i <= 8 &&
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    sm2_mont_base_table_correct &&
	    UCharArray::full(&(k->v[0]), 8, sublist(0, 8, byte_list)) *
	    UCharArray::full(&(k->v[1]), 8, sublist(8, 16, byte_list)) *
	    UCharArray::full(pk, 8, sublist(16, 24, byte_list)) *
	    UCharArray::full(&(k->v[3]), 8, sublist(24, 32, byte_list)) *
	    store_mont_jpoint(
	      &K0, sm2_point_mul(sm2_scalar_chunk(K, 0, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K1, sm2_point_mul(sm2_scalar_chunk(K, 1, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K2, sm2_point_mul(sm2_scalar_chunk(K, 2, i), SM2_G_POINT)) *
	    UInt64Array::undef_full(&(K3.x.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.y.v[0]), 4) *
	    UInt64Array::undef_full(&(K3.z.v[0]), 4) *
	    UInt64Array::undef_full(&(result->x.v[0]), 4) *
	    UInt64Array::undef_full(&(result->y.v[0]), 4) *
	    UInt64Array::undef_full(&(result->z.v[0]), 4) *
	    StructAFPointArray::full(
	      &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	      sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA)) *
	    store_sm2_p * store_sm2_rhop *
	    store_bn_zero * store_montg_one
	 */
	for (i = 1; i < 8; i++)
	{
		/*@ Given PT B */
		byteIdx = pk[i];
		/*@
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  Zlength(byte_list) == 32 &&
		  u8_list_bounded(byte_list) && 1 <= i && i < 8 &&
		  byteIdx == sublist(16, 24, byte_list)[i]
		  which implies
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  0 <= byteIdx && byteIdx < 256
		 */
		pT = &(g_montg_AFTable_for_base_point_mul[2][i][byteIdx]);
		montg_add_jpoint_and_apoint_ex(&K2, pT, &K2)
		/*@ where (r_eq_a)
		      P1 = sm2_point_mul(sm2_scalar_chunk(K, 2, i), SM2_G_POINT),
		      P2 = sm2_point_mul(sm2_table_term(byteIdx, 2, i), SM2_G_POINT)
		 */;
	}
	/*@ do basepoint_bytes_alias_to_canonical */
	// k[3]
	pk = (uint8_t*)(k->v + 3);
	/*@ do basepoint_bytes_alias_to_local */
	byteIdx = pk[0];
	/*@
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  Zlength(byte_list) == 32 &&
	  u8_list_bounded(byte_list) &&
	  byteIdx == sublist(24, 32, byte_list)[0]
	  which implies
	  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
	  0 <= byteIdx && byteIdx < 256
	 */
	pT = &(g_montg_AFTable_for_base_point_mul[3][0][byteIdx]);
	montg_apoint_to_jpoint2(pT, &K3)
	/*@ where (point_non_alias)
	      P = sm2_point_mul(sm2_table_term(byteIdx, 3, 0), SM2_G_POINT)
	 */;
	/*@ Inv Assert
	  exists PT B,
	    k == k@pre && result == result@pre &&
	    pk == &(k->v[3]) && pT == PT && byteIdx == B &&
	    1 <= i && i <= 8 &&
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    sm2_mont_base_table_correct &&
	    UCharArray::full(&(k->v[0]), 8, sublist(0, 8, byte_list)) *
	    UCharArray::full(&(k->v[1]), 8, sublist(8, 16, byte_list)) *
	    UCharArray::full(&(k->v[2]), 8, sublist(16, 24, byte_list)) *
	    UCharArray::full(pk, 8, sublist(24, 32, byte_list)) *
	    store_mont_jpoint(
	      &K0, sm2_point_mul(sm2_scalar_chunk(K, 0, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K1, sm2_point_mul(sm2_scalar_chunk(K, 1, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K2, sm2_point_mul(sm2_scalar_chunk(K, 2, 8), SM2_G_POINT)) *
	    store_mont_jpoint(
	      &K3, sm2_point_mul(sm2_scalar_chunk(K, 3, i), SM2_G_POINT)) *
	    UInt64Array::undef_full(&(result->x.v[0]), 4) *
	    UInt64Array::undef_full(&(result->y.v[0]), 4) *
	    UInt64Array::undef_full(&(result->z.v[0]), 4) *
	    StructAFPointArray::full(
	      &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	      sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA)) *
	    store_sm2_p * store_sm2_rhop *
	    store_bn_zero * store_montg_one
	 */
	for (i = 1; i < 8; i++)
	{
		/*@ Given PT B */
		byteIdx = pk[i];
		/*@
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  Zlength(byte_list) == 32 &&
		  u8_list_bounded(byte_list) && 1 <= i && i < 8 &&
		  byteIdx == sublist(24, 32, byte_list)[i]
		  which implies
		  i == i && byteIdx == byteIdx && pk == pk && pT == pT &&
		  0 <= byteIdx && byteIdx < 256
		 */
		pT = &(g_montg_AFTable_for_base_point_mul[3][i][byteIdx]);
		montg_add_jpoint_and_apoint_ex(&K3, pT, &K3)
		/*@ where (r_eq_a)
		      P1 = sm2_point_mul(sm2_scalar_chunk(K, 3, i), SM2_G_POINT),
		      P2 = sm2_point_mul(sm2_table_term(byteIdx, 3, i), SM2_G_POINT)
		 */;
	}
	/*@ do basepoint_bytes_alias_to_canonical */
	montg_add_jpoint_ex(&K0, &K1, &K0)
	/*@ where (r_eq_a)
	      P1 = sm2_point_mul(sm2_scalar_chunk(K, 0, 8), SM2_G_POINT),
	      P2 = sm2_point_mul(sm2_scalar_chunk(K, 1, 8), SM2_G_POINT)
	 */;
	/*@
	  store_mont_jpoint(
	    &K0,
	    sm2_point_add(
	      sm2_point_mul(sm2_scalar_chunk(K, 0, 8), SM2_G_POINT),
	      sm2_point_mul(sm2_scalar_chunk(K, 1, 8), SM2_G_POINT)))
	  which implies
	  store_mont_jpoint(
	    &K0, sm2_point_mul(sm2_scalar_prefix(K, 16), SM2_G_POINT))
	 */
	montg_add_jpoint_ex(&K0, &K2, &K0)
	/*@ where (r_eq_a)
	      P1 = sm2_point_mul(sm2_scalar_prefix(K, 16), SM2_G_POINT),
	      P2 = sm2_point_mul(sm2_scalar_chunk(K, 2, 8), SM2_G_POINT)
	 */;
	/*@
	  store_mont_jpoint(
	    &K0,
	    sm2_point_add(
	      sm2_point_mul(sm2_scalar_prefix(K, 16), SM2_G_POINT),
	      sm2_point_mul(sm2_scalar_chunk(K, 2, 8), SM2_G_POINT)))
	  which implies
	  store_mont_jpoint(
	    &K0, sm2_point_mul(sm2_scalar_prefix(K, 24), SM2_G_POINT))
	 */
	montg_add_jpoint_ex(&K0, &K3, result)
	/*@ where (non_alias)
	      P1 = sm2_point_mul(sm2_scalar_prefix(K, 24), SM2_G_POINT),
	      P2 = sm2_point_mul(sm2_scalar_chunk(K, 3, i), SM2_G_POINT)
	 */;

	/*@ do basepoint_bytes_merge32 */
	/*@ do basepoint_bytes_close_scalar */
	/*@
	  sm2_mont_base_table_correct &&
	  StructAFPointArray::full(
	    &g_montg_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	    sm2_table_flatten(SM2_MONT_BASE_TABLE_DATA))
	  which implies store_sm2_mont_base_point_table
	 */
}
