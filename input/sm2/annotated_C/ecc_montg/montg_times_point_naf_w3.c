/* Verification copy of YCrypt/sm2/ecc_montg.c::montg_times_point_naf_w3. */

#include "../include/ecc.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_point_copy_steps.strategies" */
/*@ include strategies "../strategy/ecc_point_overwrite.strategies" */
/*@ include strategies "../strategy/wnaf3_precomp_points.strategies" */
/*@ include strategies "../strategy/wnaf3_predicate_cancellation.strategies" */

void montg_pre_compute_naf_w3(const AFPoint* apoint, AFPoint positive[4], AFPoint negative[4])
/*@ non_alias
    With (PrecompPoint : ec_point)
    Require
      PrecompPoint != ECInfinity &&
      store_afpoint(apoint, PrecompPoint) *
      wnaf3_precomp_undef(positive, negative) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
    Ensure
      store_afpoint(apoint, PrecompPoint) *
      store_mont_wnaf3_precomp(positive, negative, PrecompPoint) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
 */;

void get_naf_w3(const u32* scalar, int8_t digits[257])
/*@ non_alias
    With (Scalar : Z)
    Require store_fn(scalar, Scalar) * CharArray::undef_full(digits, 257)
    Ensure store_fn(scalar, Scalar) * store_wnaf3(digits, Scalar)
 */;

static inline void montg_set_jpoint_to_zero(JPoint* point)
/*@ point
    Require
      store_montg_one *
      UInt64Array::undef_full(&(point->x.v[0]), 4) *
      UInt64Array::undef_full(&(point->y.v[0]), 4) *
      UInt64Array::undef_full(&(point->z.v[0]), 4)
    Ensure
      store_montg_one *
      store_mont_jpoint(point, ECInfinity)
 */;

int montg_apoint_to_jpoint2(const AFPoint* point, JPoint* result)
/*@ point_non_alias
    With (InputPoint : ec_point)
    Require
      store_mont_afpoint(point, InputPoint) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_bn_zero * store_montg_one
    Ensure
      __return == 1 &&
      store_mont_afpoint(point, InputPoint) *
      store_mont_jpoint(result, InputPoint) *
      store_bn_zero * store_montg_one
 */;

void montg_double_jpoint_ex(const JPoint* point, JPoint* result)
/*@ in_place
    With (InputPoint : ec_point)
    Require
      result == point &&
      store_mont_jpoint(point, InputPoint) *
      store_sm2_p * store_sm2_rhop
    Ensure
      result == point &&
      store_mont_jpoint(result, sm2_point_double(InputPoint)) *
      store_sm2_p * store_sm2_rhop
 */;

void montg_add_jpoint_and_apoint_ex(
    const JPoint* left, const AFPoint* right, JPoint* result)
/*@ r_eq_a
    With (Left Right : ec_point)
    Require
      result == left &&
      store_mont_jpoint(left, Left) *
      store_mont_afpoint(right, Right) *
      store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
    Ensure
      result == left &&
      store_mont_jpoint(result, sm2_point_add(Left, Right)) *
      store_mont_afpoint(right, Right) *
      store_bn_zero * store_montg_one * store_sm2_p * store_sm2_rhop
 */;

inline void CopyJPoint(const JPoint* source, JPoint* destination)
/*@ mont_non_alias
    With (CopiedPoint : ec_point)
    Require
      store_mont_jpoint(source, CopiedPoint) *
      UInt64Array::undef_full(&(destination->x.v[0]), 4) *
      UInt64Array::undef_full(&(destination->y.v[0]), 4) *
      UInt64Array::undef_full(&(destination->z.v[0]), 4)
    Ensure
      store_mont_jpoint(source, CopiedPoint) *
      store_mont_jpoint(destination, CopiedPoint)
 */;

void montg_times_point_naf_w3(const AFPoint* P, const u32* k, JPoint* result)
/*@ non_alias
    With (BasePoint : ec_point) (K : Z)
    Require
      BasePoint != ECInfinity &&
      store_afpoint(P, BasePoint) * store_fn(k, K) *
      UInt64Array::undef_full(&(result->x.v[0]), 4) *
      UInt64Array::undef_full(&(result->y.v[0]), 4) *
      UInt64Array::undef_full(&(result->z.v[0]), 4) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
    Ensure
      store_afpoint(P, BasePoint) * store_fn(k, K) *
      store_mont_jpoint(result, sm2_point_mul(K, BasePoint)) *
      store_sm2_h * store_sm2_p * store_sm2_rhop *
      store_bn_zero * store_montg_one
 */
/*@ non_alias */
{
	int i = 0;
	int8_t ki = 0;
	int8_t naf_k[257] = { 0 };
	JPoint Q;
	/* Verification normalization: the production function uses function-local
	 * static tables.  Automatic tables preserve the per-call contents used by
	 * this function while keeping their ownership private to this proof. */
	AFPoint PT[4];
	/*@ do wnaf3_positive_array_prepare */
	AFPoint NT[4];
	/*@ do wnaf3_negative_array_prepare */
	/*@ do wnaf3_arrays_combine */
	montg_pre_compute_naf_w3(P, PT, NT)
	/*@ where (non_alias) PrecompPoint = BasePoint */;
	/*@ do wnaf3_precomp_normalize_base */
	/*@ do wnaf3_buffer_to_undef */
	get_naf_w3(k, naf_k)
	/*@ where (non_alias) Scalar = K */;
	/*@ do open_store_wnaf3 */
	/*@ do wnaf3_digits_normalize_base */
	montg_set_jpoint_to_zero(&Q);

	// First time
	ki = naf_k[256];
	/*@ exists initial_digits first_digit,
	      first_digit == Znth(256, initial_digits, 0) &&
	      wnaf3_representation(K, initial_digits) &&
	      store(&ki, first_digit) *
	      CharArray::full(naf_k, 257, initial_digits)
	    which implies
	      exists initial_digits first_digit,
	        first_digit == Znth(256, initial_digits, 0) &&
	        wnaf3_representation(K, initial_digits) &&
	        wnaf3_digit(first_digit) &&
	        store(&ki, first_digit) *
	        CharArray::full(naf_k, 257, initial_digits)
	 */
	/*@ Given initial_digits first_digit */
	if (ki > 0)
	{
		/*@ do wnaf3_focus_positive */
		montg_apoint_to_jpoint2(PT + ki, &Q)
		/*@ where (point_non_alias)
		      InputPoint = sm2_point_mul(ki, BasePoint) */;
		/*@ do wnaf3_restore_positive */
		/*@ 0 <= K &&
		      0 <= wnaf3_value(sublist(256, 257, initial_digits)) &&
		      sm2_point_mul(first_digit, BasePoint) ==
		        sm2_point_mul(
		          wnaf3_value(sublist(256, 257, initial_digits)), BasePoint)
		 */
	}
	else if(ki < 0)
	{
		/*@ do wnaf3_focus_negative */
		montg_apoint_to_jpoint2(NT + (-ki), &Q)
		/*@ where (point_non_alias)
		      InputPoint =
		        sm2_point_negate(sm2_point_mul(-ki, BasePoint)) */;
		/*@ do wnaf3_restore_negative */
		/*@ 0 <= K &&
		      0 <= wnaf3_value(sublist(256, 257, initial_digits)) &&
		      sm2_point_negate(sm2_point_mul(-first_digit, BasePoint)) ==
		        sm2_point_mul(
		          wnaf3_value(sublist(256, 257, initial_digits)), BasePoint)
		 */
	}
	else
	{
		/*@ 0 <= K &&
		      0 <= wnaf3_value(sublist(256, 257, initial_digits)) &&
		      ECInfinity ==
		        sm2_point_mul(
		          wnaf3_value(sublist(256, 257, initial_digits)), BasePoint)
		 */
	}
	/*@ exists digits,
	      0 <= K &&
	      0 <= wnaf3_value(sublist(256, 257, digits)) &&
	      wnaf3_representation(K, digits) &&
	      P == P@pre && k == k@pre && result == result@pre &&
	      store_mont_jpoint(&Q,
	        sm2_point_mul(
	          wnaf3_value(sublist(256, 257, digits)), BasePoint)) *
	      CharArray::full(naf_k, 257, digits) *
		      store_mont_wnaf3_precomp(PT, NT, BasePoint) *
		      wnaf3_precomp_unused(PT, NT) *
	      store_afpoint(P@pre, BasePoint) * store_fn(k@pre, K) *
	      UInt64Array::undef_full(&(result@pre->x.v[0]), 4) *
	      UInt64Array::undef_full(&(result@pre->y.v[0]), 4) *
	      UInt64Array::undef_full(&(result@pre->z.v[0]), 4) *
	      store_sm2_h * store_sm2_p * store_sm2_rhop *
	      store_bn_zero * store_montg_one * has_permission(&ki)
	 */
	
	// Left 256 times
	/*@ Inv Assert
	    exists digits Acc,
	      P == P@pre && k == k@pre && result == result@pre &&
	      -1 <= i && i <= 255 &&
	      0 <= K &&
	      0 <= wnaf3_value(sublist(i + 1, 257, digits)) &&
	      wnaf3_representation(K, digits) &&
	      Acc == sm2_point_mul(
	        wnaf3_value(sublist(i + 1, 257, digits)), BasePoint) &&
	      store_afpoint(P@pre, BasePoint) * store_fn(k@pre, K) *
	      store_mont_jpoint(&Q, Acc) *
		      store_mont_wnaf3_precomp(PT, NT, BasePoint) *
		      wnaf3_precomp_unused(PT, NT) *
	      CharArray::full(naf_k, 257, digits) *
	      UInt64Array::undef_full(&(result@pre->x.v[0]), 4) *
	      UInt64Array::undef_full(&(result@pre->y.v[0]), 4) *
	      UInt64Array::undef_full(&(result@pre->z.v[0]), 4) *
	      store_sm2_h * store_sm2_p * store_sm2_rhop *
	      store_bn_zero * store_montg_one * has_permission(&ki)
	 */
	for (i = 255; i >= 0; i--)
	{
		/*@ Given digits Acc */
		montg_double_jpoint_ex(&Q, &Q)
		/*@ where (in_place) InputPoint = Acc */;
		ki = naf_k[i];
		/*@ exists digit,
		      digit == Znth(i, digits, 0) &&
		      0 <= i && i < 256 &&
		      wnaf3_representation(K, digits) &&
		      store(&ki, digit) *
		      CharArray::full(naf_k, 257, digits)
		    which implies
		      exists digit,
		        digit == Znth(i, digits, 0) &&
		        0 <= i && i < 256 &&
		        wnaf3_representation(K, digits) &&
		        wnaf3_digit(digit) &&
		        store(&ki, digit) *
		        CharArray::full(naf_k, 257, digits)
		 */
		/*@ Given digit */
		if (ki)
		{
			if (ki > 0)
			{
				/*@ do wnaf3_focus_positive */
				montg_add_jpoint_and_apoint_ex(&Q, PT + ki, &Q)
				/*@ where (r_eq_a)
				      Left = sm2_point_double(Acc),
				      Right = sm2_point_mul(digit, BasePoint) */;
				/*@ do wnaf3_restore_positive */
				/*@ 0 <= wnaf3_value(sublist(i, 257, digits)) &&
				      sm2_point_add(sm2_point_double(Acc),
				        sm2_point_mul(digit, BasePoint)) ==
				        sm2_point_mul(
				          wnaf3_value(sublist(i, 257, digits)), BasePoint)
				 */
			}
			else
			{
				/*@ digit < 0 by local */
				/*@ do wnaf3_focus_negative */
				montg_add_jpoint_and_apoint_ex(&Q, NT + (-ki), &Q)
				/*@ where (r_eq_a)
				      Left = sm2_point_double(Acc),
				      Right =
				        sm2_point_negate(sm2_point_mul(-digit, BasePoint)) */;
				/*@ do wnaf3_restore_negative */
				/*@ 0 <= wnaf3_value(sublist(i, 257, digits)) &&
				      sm2_point_add(sm2_point_double(Acc),
				        sm2_point_negate(sm2_point_mul(-digit, BasePoint))) ==
				        sm2_point_mul(
				          wnaf3_value(sublist(i, 257, digits)), BasePoint)
				 */
			}
		}
		else
		{
			/*@ 0 <= wnaf3_value(sublist(i, 257, digits)) &&
			      sm2_point_double(Acc) ==
			        sm2_point_mul(
			          wnaf3_value(sublist(i, 257, digits)), BasePoint)
			 */
			}
		}
		/*@ Given digits Acc */
		/*@ Acc == sm2_point_mul(K, BasePoint) */
		CopyJPoint(&Q, result)
	/*@ where (mont_non_alias) CopiedPoint = Acc */;
	/*@ do wnaf3_arrays_release */
}
