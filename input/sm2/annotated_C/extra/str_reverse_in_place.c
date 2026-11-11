/* Verification copy of YCrypt/sm2/extra.c::str_reverse_in_place. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/byte_pointer_views.strategies" */

void str_reverse_in_place(u1 *str, int len)
/*@ With bytes
    Require
      0 < len &&
      store_bytes(str, len, bytes)
    Ensure
      store_bytes(str, len, rev(bytes))
 */
{
	u1 *p1 = str;
	u1 *p2 = str + len - 1;

	/*@ do open_store_bytes */
	/*@ Inv Assert
	      exists current index,
	        str == str@pre && len == len@pre &&
	        p1 == str + index * sizeof(unsigned char) &&
		        p2 == str + (len - 1 - index) * sizeof(unsigned char) &&
		        Zlength(current) == len &&
		        u8_list_bounded(bytes) &&
		        0 < len && 0 <= index && index < len &&
	        2 * index <= len &&
	        byte_reverse_loop_state(bytes, current, index) &&
	        UCharArray::full(str, len, current)
	 */
	while (p1 < p2)
	{
		/*@ Given current index */
		u1 tmp = *p1;
		*p1 = *p2;
		p1++;
		*p2 = tmp;
		p2--;
	}
}
