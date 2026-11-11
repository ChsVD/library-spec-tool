/* Verification copy of YCrypt/sm2/extra.c::u1_to_u32. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/byte_memory_views.strategies" */

void *memcpy(void *dest, const void *src, size_t count)
/*@ With bytes
    Require
      0 <= count &&
      UCharArray::undef_full(dest, count) *
      store_bytes(src, count, bytes)
    Ensure
      __return == dest &&
      store_bytes(dest, count, bytes) *
      store_bytes(src, count, bytes)
 */
;

void str_reverse_in_place(u1 *str, int len)
/*@ With bytes
    Require
      0 < len &&
      store_bytes(str, len, bytes)
    Ensure
      store_bytes(str, len, rev(bytes))
 */
;

void u1_to_u32(const u1 input[32], u32 *result)
/*@ With bytes
    Require
      store_bytes(input, 32, bytes) *
      UndefStructPredu32(result)
    Ensure
      store_bytes(input, 32, bytes) *
      store_u256(result, be_u8_list_value(bytes))
 */
{
	u1 tmp[32];
	memcpy(tmp, input, 32);
	str_reverse_in_place(tmp, 32);
	/*@ do open_undef_u256_bytes */
	memcpy(result, tmp, 32);
	/*@ u8_list_value(rev(bytes)) == be_u8_list_value(bytes) */
	/*@ do close_store_u256_bytes */
}
