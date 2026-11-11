/* Verification copy of YCrypt/sm2/sm2.c::sm2_get_id_digest. */

#include "../include/sm2_protocol.h"
/*@ include strategies "../strategy/sm2_representation.strategies" */
/*@ include strategies "../strategy/array_bridges.strategies" */
/*@ include strategies "../strategy/ecc_representation.strategies" */
/*@ include strategies "../strategy/ecc_constants.strategies" */
/*@ include strategies "../strategy/byte_memory_views.strategies" */
/*@ include strategies "../strategy/sm2_protocol_views.strategies" */
/*@ include strategies "../strategy/sm2_za_buffers.strategies" */

void *memcpy(void *dest, const void *src, size_t count)
/*@ dst_segment
    With DestBase DestOffset DestCapacity Bytes
    Require
      dest == DestBase + DestOffset * sizeof(unsigned char) &&
      0 <= count && 0 <= DestOffset &&
      DestOffset + count <= DestCapacity &&
      UCharArray::undef_seg(
        DestBase, DestOffset, DestCapacity) *
      store_bytes(src, count, Bytes)
    Ensure
      __return == dest &&
      Zlength(Bytes) == count && u8_list_bounded(Bytes) &&
      UCharArray::seg(
        DestBase, DestOffset, DestOffset + count, Bytes) *
      UCharArray::undef_seg(
        DestBase, DestOffset + count, DestCapacity) *
      store_bytes(src, count, Bytes)
 */
/*@ segments
    With DestBase DestOffset DestCapacity
         SrcBase SrcOffset Bytes
    Require
      dest == DestBase + DestOffset * sizeof(unsigned char) &&
      src == SrcBase + SrcOffset * sizeof(unsigned char) &&
      0 <= count && 0 <= DestOffset &&
      DestOffset + count <= DestCapacity &&
      Zlength(Bytes) == count && u8_list_bounded(Bytes) &&
      UCharArray::undef_seg(
        DestBase, DestOffset, DestCapacity) *
      UCharArray::seg(
        SrcBase, SrcOffset, SrcOffset + count, Bytes)
    Ensure
      __return == dest &&
      Zlength(Bytes) == count && u8_list_bounded(Bytes) &&
      UCharArray::seg(
        DestBase, DestOffset, DestOffset + count, Bytes) *
      UCharArray::undef_seg(
        DestBase, DestOffset + count, DestCapacity) *
      UCharArray::seg(
        SrcBase, SrcOffset, SrcOffset + count, Bytes)
 */;

void str_reverse_in_place(u1 *str, int len)
/*@ With Bytes
    Require
      0 < len &&
      store_bytes(str, len, Bytes)
    Ensure
      store_bytes(str, len, rev(Bytes))
 */;

size_t sm3(const u1 *data, size_t datalen, u1 dgst[32])
/*@ With Message
    Require
      sm3_digest_input_aligned(data, datalen) &&
      aligned_4(dgst) &&
      store_bytes(data, datalen, Message) *
      UCharArray::undef_full(dgst, 32) *
      store_sm3_ti
    Ensure
      __return == 32 &&
      store_bytes(data, datalen, Message) *
      store_bytes(dgst, 32, sm3_digest_bytes(Message)) *
      store_sm3_ti
 */;

void alignas_uint32_t(const void *address)
/*@ Require emp
    Ensure aligned_4(address) && emp
 */;

int sm2_get_id_digest(
    u1 result[32], const u1 *id, size_t id_len, const PubKey *pubkey)
/*@ With ID (P : ec_point)
    Require
      sm2_id_digest_output_aligned(result, id_len) &&
      store_bytes(id, id_len, ID) *
      store_afpoint(pubkey, P) *
      UCharArray::undef_full(result, 32) *
      store_sm2_za_globals
    Ensure
      (id_len <= 50 && __return == 0 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       store_sm2_za(
         result, ID, P, sm2_za_digest(ID, P)) *
       store_sm2_za_globals)
      ||
      (id_len > 50 && __return == -1 &&
       store_bytes(id, id_len, ID) *
       store_afpoint(pubkey, P) *
       UCharArray::undef_full(result, 32) *
       store_sm2_za_globals)
 */
{
	if (id_len > 50)
	{
		return -1;
	}
	u1 total[250];
	u1 charlist[192];
	alignas_uint32_t(total);

	/*@ do open_sm2_za_globals */
	/*@ do open_sm2_g */
	/*@ do open_afpoint */
	/*@ do sm2_point_coordinates */
	/*@ do open_afpoint_fields */
	/*@ do open_sm2_a */
	/*@ do open_sm2_b */
	/*@ do open_store_fp */
	/*@ do open_store_u256_bytes */
	/*@ do start_uchar_mixed_250 */

	total[0] = ((id_len * 8) >> 8) % 256;
	total[1] = (id_len * 8) % 256;
	/*@ do materialize_uchar_prefix2 */
	/*@
	  UCharArray::seg(
	    total, 0, 2, sm2_entla_bytes(id_len))
	 */
	/*@ 2 + id_len <= 250 */
	memcpy(total + 2, id, id_len)
	/*@ where (dst_segment)
	      DestBase = total, DestOffset = 2, DestCapacity = 250 */;

	memcpy(charlist, &SM2_a, 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 0, DestCapacity = 192 */;
	str_reverse_in_place(charlist, 32);
	/*@ do restore_uchar_segment */

	memcpy(charlist + 32, &SM2_b, 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 32, DestCapacity = 192 */;
	str_reverse_in_place(charlist + 32, 32);
	/*@ do restore_uchar_segment */

	memcpy(charlist + 64, &(SM2_G.x), 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 64, DestCapacity = 192 */;
	str_reverse_in_place(charlist + 64, 32);
	/*@ do restore_uchar_segment */

	memcpy(charlist + 96, &(SM2_G.y), 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 96, DestCapacity = 192 */;
	str_reverse_in_place(charlist + 96, 32);
	/*@ do restore_uchar_segment */

	memcpy(charlist + 128, &(pubkey->x), 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 128, DestCapacity = 192 */;
	str_reverse_in_place(charlist + 128, 32);
	/*@ do restore_uchar_segment */

	memcpy(charlist + 160, &(pubkey->y), 32)
	/*@ where (dst_segment)
	      DestBase = charlist, DestOffset = 160, DestCapacity = 192 */;
	str_reverse_in_place(charlist + 160, 32);
	/*@ do restore_uchar_segment */
	/*@ do merge_uchar_segments */
	/*@
	  UCharArray::seg(
	    charlist, 0, 192,
	    app(u256_to_be_bytes(SM2_A_Z),
	    app(u256_to_be_bytes(SM2_B_Z),
	    app(u256_to_be_bytes(sm2_point_x(SM2_G_POINT)),
	    app(u256_to_be_bytes(sm2_point_y(SM2_G_POINT)),
	    app(u256_to_be_bytes(sm2_point_x(P)),
	        u256_to_be_bytes(sm2_point_y(P))))))))
	 */

	/*@ do close_store_u256_bytes */
	/*@ 2 + id_len + 192 <= 250 */
	memcpy(total + 2 + id_len, charlist, 192)
	/*@ where (segments)
	      DestBase = total, DestOffset = 2 + id_len,
	      DestCapacity = 250,
	      SrcBase = charlist, SrcOffset = 0 */;
	/*@ do merge_uchar_segments */
	/*@ do close_uchar_seg0 */
	/*@
	  store_bytes(
	    total, 2 + id_len + 192, sm2_za_input(ID, P))
	 */
	sm3(total, 2 + id_len + 192, result);
	/*@ do forget_uchar_full */
	/*@ do forget_uchar_prefix */
	return 0;
}
