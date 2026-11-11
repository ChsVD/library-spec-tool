/* Verification copy of YCrypt/sm2/ecc_basepoint_mul.c::ML_mul_basepoint. */

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

extern const AFPoint g_AFTable_for_base_point_mul[4][8][256];

JPoint* memset(JPoint* dest, int c, size_t n)
/*@ With (P : ec_point)
    Require
      c == 0 && n == sizeof(struct JPoint) &&
      store_jpoint_with_canonical_infinity(dest, P)
    Ensure
      __return == dest && store_jpoint_fields(dest, 0, 0, 0)
 */;

JPoint* memcpy(JPoint* dest, const JPoint* src, size_t n)
/*@ With (P : ec_point)
    Require
      n == sizeof(struct JPoint) &&
      store_jpoint_with_canonical_infinity(src, P) *
      UInt64Array::undef_full(&(dest->x.v[0]), 4) *
      UInt64Array::undef_full(&(dest->y.v[0]), 4) *
      UInt64Array::undef_full(&(dest->z.v[0]), 4)
    Ensure
      __return == dest &&
      store_jpoint_with_canonical_infinity(src, P) *
      store_jpoint_with_canonical_infinity(dest, P)
 */;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      (P1 == ECInfinity || P2 == ECInfinity ||
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p * store_sm2_rhop * store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p * store_sm2_rhop * store_jpoint_zero
 */;

void add_JPoint_and_AFPoint(
    const JPoint* point1, const AFPoint* point2, JPoint* result)
/*@ canonical_finite_guard_r_eq_point1 <= canonical_r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      ((P1 != ECInfinity && P2 != ECInfinity) => P1 != P2) &&
      ((P1 != ECInfinity && P2 != ECInfinity) =>
       sm2_point_add(P1, P2) != ECInfinity) &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_afpoint(point2, P2) *
      store_sm2_p * store_sm2_rhop * store_jpoint_zero
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_afpoint(point2, P2) *
      store_sm2_p * store_sm2_rhop * store_jpoint_zero
 */;

void add_JPoint(const JPoint* point1, const JPoint* point2, JPoint* result)
/*@ r_eq_point1
    With (P1 P2 : ec_point)
    Require
      result == point1 &&
      store_jpoint_with_canonical_infinity(point1, P1) *
      store_jpoint_with_canonical_infinity(point2, P2) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == point1 &&
      store_jpoint_with_canonical_infinity(point2, P2) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_add(P1, P2)) *
      store_jpoint_zero * store_sm2_inv2p *
      store_sm2_p * store_sm2_rhop
 */;

void ML_mul_basepoint(const u32* k, JPoint* result)
/*@ non_alias
    With K
    Require
      store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_jpoint_zero * store_sm2_inv2p
    Ensure
      store_fn(k, K) *
      store_jpoint_with_canonical_infinity(
        result, sm2_point_mul(K, SM2_G_POINT)) *
      store_sm2_base_point_table *
      store_sm2_p * store_sm2_rhop *
      store_jpoint_zero * store_sm2_inv2p
 */
{
	int i = 0, j = 0;
	/*@ do open_jpoint_zero */
	/*@ do materialize_jpoint_record */
	JPoint Tr = JPoint_ZERO;
	JPoint T = JPoint_ZERO;
	uint8_t* pByte = NULL, byte;
	AFPoint *pTable = NULL;

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
	/*@
	  store_sm2_base_point_table
	  which implies
	  sm2_base_table_correct(SM2_BASE_TABLE_DATA) &&
	  StructAFPointArray::full(
	    &g_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	    sm2_table_flatten(SM2_BASE_TABLE_DATA))
	 */

	/*@ Inv Assert
	  exists (TP : ec_point) PB PA J,
	    k == k@pre && result == result@pre &&
	    pByte == PB && pTable == PA && j == J &&
	    0 <= i && i <= 4 &&
	    0 <= K && K < SM2_N_Z &&
	    Zlength(byte_list) == 32 &&
	    u8_list_bounded(byte_list) &&
	    u8_list_value(byte_list) == K &&
	    aligned_4(&(k->v[0])) &&
	    sm2_base_table_correct(SM2_BASE_TABLE_DATA) &&
	    UCharArray::full(&(k->v[0]), 32, byte_list) *
	    store_jpoint_with_canonical_infinity(
	      &Tr, sm2_point_mul(sm2_scalar_prefix(K, 8 * i), SM2_G_POINT)) *
	    store_jpoint_with_canonical_infinity(&T, TP) *
	    UInt64Array::undef_full(&(result->x.v[0]), 4) *
	    UInt64Array::undef_full(&(result->y.v[0]), 4) *
	    UInt64Array::undef_full(&(result->z.v[0]), 4) *
	    StructAFPointArray::full(
	      &g_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	      sm2_table_flatten(SM2_BASE_TABLE_DATA)) *
	    store_sm2_p * store_sm2_rhop *
	    store_jpoint_zero * store_sm2_inv2p *
	    has_permission(&byte)
	 */
	for (i = 0; i < 4; i++)
	{
		/*@ Given TP PB PA J */
		pByte = (uint8_t*)(&(k->v[i]));

		// Reset T to JPoint_ZERO
		memset(&T, 0, sizeof(T)) /*@ where P = TP */;
		/*@
		  store_jpoint_fields(&T, 0, 0, 0)
		  which implies
		  UInt64Array::full(
		    &(T.x.v[0]), 4, cons(0, cons(0, cons(0, cons(0, nil))))) *
		  UInt64Array::full(
		    &(T.y.v[0]), 4, cons(0, cons(0, cons(0, cons(0, nil))))) *
		  UInt64Array::full(
		    &(T.z.v[0]), 4, cons(0, cons(0, cons(0, cons(0, nil)))))
		 */
		T.x.v[0] = 1;
		T.y.v[0] = 1;

		/*@ do basepoint_bytes_focus_chunk */

		/*@ Inv Assert
			  exists PATable,
			  k == k@pre && result == result@pre && pTable == PATable &&
		  0 <= i && i < 4 && 0 <= j && j <= 8 &&
		  0 <= K && K < SM2_N_Z &&
		  Zlength(byte_list) == 32 &&
		  u8_list_bounded(byte_list) &&
		  u8_list_value(byte_list) == K &&
		  aligned_4(&(k->v[0])) &&
		  sm2_base_table_correct(SM2_BASE_TABLE_DATA) &&
		  UCharArray::full(
		    &(k->v[0]), 8 * i, sublist(0, 8 * i, byte_list)) *
			  UCharArray::full(
			    &(k->v[i]), 8, sublist(8 * i, 8 * i + 8, byte_list)) *
			  UCharArray::full(
			    &(k->v[i + 1]), 32 - (8 * i + 8),
			    sublist(8 * i + 8, 32, byte_list)) *
			  store(&pByte, unsigned char*, &(k->v[i])) *
			  store_jpoint_with_canonical_infinity(
		    &Tr, sm2_point_mul(sm2_scalar_prefix(K, 8 * i), SM2_G_POINT)) *
		  store_jpoint_with_canonical_infinity(
		    &T, sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT)) *
		  UInt64Array::undef_full(&(result->x.v[0]), 4) *
		  UInt64Array::undef_full(&(result->y.v[0]), 4) *
		  UInt64Array::undef_full(&(result->z.v[0]), 4) *
		  StructAFPointArray::full(
		    &g_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
		    sm2_table_flatten(SM2_BASE_TABLE_DATA)) *
		  store_sm2_p * store_sm2_rhop *
		  store_jpoint_zero * store_sm2_inv2p *
		  has_permission(&byte)
		 */
		for (j = 0; j < 8; j++)
		{
			/*@ Given PATable */
			byte = pByte[j];
			/*@
			  i == i && j == j && byte == byte &&
			  pByte == pByte && pTable == pTable &&
			  Zlength(byte_list) == 32 &&
			  u8_list_bounded(byte_list) &&
			  0 <= i && i < 4 && 0 <= j && j < 8 &&
			  byte == sublist(8 * i, 8 * i + 8, byte_list)[j]
			  which implies
			  i == i && j == j && byte == byte &&
			  pByte == pByte && pTable == pTable &&
			  0 <= byte && byte < 256
			 */
			pTable = (AFPoint*)&(g_AFTable_for_base_point_mul[i][j][byte]);
			/*@
			  0 <= K && K < SM2_N_Z &&
			  Zlength(byte_list) == 32 &&
			  u8_list_bounded(byte_list) &&
			  u8_list_value(byte_list) == K &&
			  0 <= i && i < 4 && 0 <= j && j < 8 &&
			  byte == sublist(8 * i, 8 * i + 8, byte_list)[j] &&
			  store_jpoint_with_canonical_infinity(
			    &T,
			    sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT)) *
			  store_afpoint(
			    pTable,
			    sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT))
			  which implies
			  ((sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT) !=
			      ECInfinity &&
			    sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT) !=
			      ECInfinity) =>
			   sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT) !=
			    sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT)) &&
			  ((sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT) !=
			      ECInfinity &&
			    sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT) !=
			      ECInfinity) =>
			   sm2_point_add(
			     sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT),
			     sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT)) !=
			     ECInfinity) &&
			  store_jpoint_with_canonical_infinity(
			    &T,
			    sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT)) *
			  store_afpoint(
			    pTable,
			    sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT))
			 */
			add_JPoint_and_AFPoint(&T, pTable, &T)
			/*@ where (canonical_finite_guard_r_eq_point1)
			      P1 = sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT),
			      P2 = sm2_point_mul(sm2_table_term(byte, i, j), SM2_G_POINT)
			 */;
		}
		/*@ do basepoint_bytes_merge_chunk */
		add_JPoint(&Tr, &T, &Tr)
		/*@ where (r_eq_point1)
		      P1 = sm2_point_mul(sm2_scalar_prefix(K, 8 * i), SM2_G_POINT),
		      P2 = sm2_point_mul(sm2_scalar_chunk(K, i, j), SM2_G_POINT)
		 */;
	}

	/*@ do basepoint_bytes_close_scalar */
	/*@
	  sm2_base_table_correct(SM2_BASE_TABLE_DATA) &&
	  StructAFPointArray::full(
	    &g_AFTable_for_base_point_mul, SM2_TABLE_RECORDS,
	    sm2_table_flatten(SM2_BASE_TABLE_DATA))
	  which implies store_sm2_base_point_table
	 */
	// Save the result
	memcpy(result, &Tr, sizeof(JPoint))
	/*@ where P = sm2_point_mul(sm2_scalar_prefix(K, 8 * i), SM2_G_POINT) */;
}
