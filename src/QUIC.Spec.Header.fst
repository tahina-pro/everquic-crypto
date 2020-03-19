module QUIC.Spec.Header
open QUIC.Spec.Base
open QUIC.Spec.PacketNumber

open LowParse.Spec.Int
open LowParse.Spec.BitSum

open LowParse.Spec.BoundedInt

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-17 *)


inline_for_extraction
type header_form_t =
  | Long
  | Short

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_form : enum header_form_t (bitfield uint8 1) = [
  Long, 1uy;
  Short, 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let fixed_bit : enum unit (bitfield uint8 1) = [
  (), 1uy;
]

inline_for_extraction
type long_packet_type_t =
  | Initial
  | ZeroRTT
  | Handshake
  | Retry

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let long_packet_type : enum long_packet_type_t (bitfield uint8 2) = [
  Initial, 0uy;
  ZeroRTT, 1uy;
  Handshake, 2uy;
  Retry, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let reserved_bits : enum unit (bitfield uint8 2) = [
  (), 0uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let packet_number_length : enum packet_number_length_t (bitfield uint8 2) = [
  1ul, 0uy;
  2ul, 1uy;
  3ul, 2uy;
  4ul, 3uy;
]

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let rrpp : bitsum' uint8 4 =
  BitSum' _ _ reserved_bits (fun _ -> BitSum' _ _ packet_number_length (fun _ -> BitStop ()))

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let first_byte : bitsum' uint8 8 =
  BitSum' _ _ header_form (function
    | Short ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitField (* spin bit *) 1 (
          BitSum' _ _ reserved_bits (fun _ ->
            BitField (* key phase *) 1 (
              BitSum' _ _ packet_number_length (fun _ ->
                BitStop ()
              )
            )
          )
        )
      )
    | Long ->
      BitSum' _ _ fixed_bit (fun _ ->
        BitSum' _ _ long_packet_type (function
          | Retry -> BitField (* unused *) 4 (BitStop ())
          | _ -> rrpp
        )
      )
  )

(*
// How to test normalization:
module T = FStar.Tactics
let f (x: FStar.UInt8.t) : Tot unit =
  assert (filter_header_byte x == true) by (
    T.norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]];
    T.fail "abc"
  )
*)

module FB = FStar.Bytes
open LowParse.Spec.Bytes

inline_for_extraction
let short_dcid_len_t = (short_dcid_len: U32.t { U32.v short_dcid_len <= 20 })

let short_dcid_len_prop
  (short_dcid_len: short_dcid_len_t)
  (h: header)
: GTot Type0
= (MShort? h ==> dcid_len h == U32.v short_dcid_len)

let packet_number_prop
  (last: last_packet_number_t)
  (h: header)
: GTot Type0
= ((~ (is_retry h)) ==> in_window (U32.v (pn_length h) - 1) (U64.v last) (U64.v (packet_number h)))

unfold
let parse_header_prop
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (m: header)
: GTot Type0
= short_dcid_len_prop short_dcid_len m /\
  packet_number_prop last m

inline_for_extraction
type header'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
= (m: header { parse_header_prop short_dcid_len last m })


#push-options "--z3rlimit 16"

inline_for_extraction
noextract
let first_byte_of_header'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (t: Type0)
  (f: (bitsum'_type first_byte -> Tot t))
  (m: header' short_dcid_len last)
: Tot t
= match m with
  | MShort spin key_phase dcid pn_length packet_number ->
    let spin : bitfield uint8 1 = if spin then 1uy else 0uy in
    let key_phase : bitfield uint8 1 = if key_phase then 1uy else 0uy in
    f (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial _ payload_length pn_length _ ->
      f (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |)
    | MZeroRTT payload_length pn_length _ ->
      f (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |)
    | MHandshake payload_length pn_length _ ->
      f (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |)
    | MRetry unused _ ->
      f (| Long, (| (), (| Retry, (unused, ()) |) |) |)
    end

#pop-options

let first_byte_of_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (m: header' short_dcid_len last)
: Tot (bitsum'_type first_byte)
= first_byte_of_header' short_dcid_len last (bitsum'_type first_byte) id m

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let common_long_t
: Type0
= (U32.t & (parse_bounded_vlbytes_t 0 20 & parse_bounded_vlbytes_t 0 20))

module Cast = FStar.Int.Cast

inline_for_extraction
let payload_and_pn_length_prop
  (pn_length: packet_number_length_t)
  (payload_and_pn_len: uint62_t)
: Tot bool
= payload_and_pn_len `U64.gte` Cast.uint32_to_uint64 pn_length

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot Type0
= (parse_filter_refine (payload_and_pn_length_prop pn_length) & packet_number_t last pn_length)

#push-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_body_type
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot Type0
= match k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length))
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (common_long_t & payload_length_pn last pn_length)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (common_long_t & parse_bounded_vlbytes_t 0 20)

open LowParse.Spec.BitSum // again, for coerce

#pop-options

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
: Tot (refine_with_tag (first_byte_of_header short_dcid_len last) k')
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    let spin = (spin = 1uy) in
    let key_phase = (key_phase = 1uy) in
    begin match coerce (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length) pl with
    | (dcid, packet_number) ->
      MShort spin key_phase dcid pn_length packet_number
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)) pl with
    | ((version, (dcid, scid)), (token, (payload_and_pn_length, packet_number))) ->
      MLong version dcid scid (MInitial token (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_and_pn_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_and_pn_length, packet_number)) ->
      MLong version dcid scid (MHandshake (payload_and_pn_length `U64.sub` Cast.uint32_to_uint64 pn_length) pn_length packet_number)
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match coerce (common_long_t & parse_bounded_vlbytes_t 0 20) pl with
    | ((version, (dcid, scid)), odcid) ->
      MLong version dcid scid (MRetry unused odcid)
    end

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let mk_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_type first_byte)
  (pl: refine_with_tag (first_byte_of_header short_dcid_len last) k')
: Tot (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k'))
= match k' with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    begin match pl with
    | MShort _ _ dcid _ pn -> coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) ((dcid, pn) <: (FB.lbytes (U32.v short_dcid_len) & packet_number_t last pn_length ))
    end
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MInitial token payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length `U64.add` Cast.uint32_to_uint64 pn_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

#pop-options

#push-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let header_synth
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (synth_case_t first_byte (header' short_dcid_len last) (first_byte_of_header short_dcid_len last) (header_body_type short_dcid_len last))
= 
  (SynthCase
    #_ #_ #_ #first_byte #_ #(first_byte_of_header short_dcid_len last) #(header_body_type short_dcid_len last)
    (mk_header short_dcid_len last)
    (fun k x y -> ())
    (mk_header_body short_dcid_len last)
    (fun k x -> ())
  )

#pop-options

let parse_common_long : parser _ common_long_t =
  parse_u32 `nondep_then` (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20)

open QUIC.Spec.VarInt

let parse_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (parser _ (payload_length_pn last pn_length))
= (parse_varint `parse_filter` payload_and_pn_length_prop pn_length) `nondep_then` parse_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (k: parser_kind & parser k (header_body_type short_dcid_len last k'))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    (| _, weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v short_dcid_len)) `nondep_then` parse_packet_number last pn_length |)
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) |)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_payload_length_pn last pn_length |)
  | (| Long, (| (), (| Retry, () |) |) |) ->
    (| _, parse_common_long `nondep_then` parse_bounded_vlbytes 0 20 |)

#pop-options

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let parse_header_kind'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot parser_kind
= parse_bitsum_kind parse_u8_kind first_byte (header_body_type short_dcid_len last) (parse_header_body short_dcid_len last)

let lp_parse_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (parser (parse_header_kind' short_dcid_len last) (header' short_dcid_len last))
= parse_bitsum
    first_byte
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    parse_u8
    (parse_header_body short_dcid_len last)

let serialize_common_long : serializer parse_common_long =
  serialize_u32 `serialize_nondep_then` (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20)

let serialize_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (serializer (parse_payload_length_pn last pn_length))
= (serialize_varint `serialize_filter` payload_and_pn_length_prop pn_length) `serialize_nondep_then` serialize_packet_number last pn_length

#push-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8 --initial_fuel 8 --initial_ifuel 8"

let serialize_header_body
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (serializer (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len)) `serialize_nondep_then` serialize_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    serialize_common_long `serialize_nondep_then` serialize_bounded_vlbytes 0 20

#pop-options

let serialize_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (serializer (lp_parse_header short_dcid_len last))
= serialize_bitsum
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)

let serialize_header_alt
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (x: header' short_dcid_len last)
: GTot bytes
= serialize_bitsum_alt
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    x

let serialize_header_eq
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (x: header' short_dcid_len last)
: Lemma
  (serialize (serialize_header short_dcid_len last) x == serialize_header_alt short_dcid_len last x)
= serialize_bitsum_eq'
    #parse_u8_kind
    #8
    #U8.t
    first_byte
    #(header' short_dcid_len last)
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    #parse_u8
    serialize_u8
    #(parse_header_body short_dcid_len last)
    (serialize_header_body short_dcid_len last)
    x

module LC = LowParse.Spec.Combinators
module LB = LowParse.Spec.Bytes
module LI = LowParse.Spec.BoundedInt
module LJ = LowParse.Spec.Int
module LL = LowParse.Spec.BitSum

(* Properties of the serializer *)

#push-options "--z3rlimit 128 --max_fuel 4 --initial_fuel 4"

let serialize_header_ext
  (cid_len1 cid_len2: short_dcid_len_t)
  (last1 last2: last_packet_number_t)
  (x: header)
: Lemma
  (requires (
    parse_header_prop cid_len1 last1 x /\
    parse_header_prop cid_len2 last2 x
  ))
  (ensures (
    serialize (serialize_header cid_len1 last1) x == serialize (serialize_header cid_len2 last2) x
  ))
= serialize_header_eq cid_len1 last1 x;
  serialize_header_eq cid_len2 last2 x;
  let tg = first_byte_of_header cid_len1 last1 x in
  assert (tg == first_byte_of_header cid_len2 last2 x);
  match x with
  | MShort spin key_phase dcid pn_length packet_number ->
    assert_norm (first_byte_of_header cid_len1 last1 (MShort spin key_phase dcid pn_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| pn_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MShort spin key_phase dcid pn_length packet_number)) == (| Short, (| (), (| (), (| pn_length, () |) |) |) |) );
    assert (cid_len1 == cid_len2);
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v cid_len1))) (serialize_packet_number last1 pn_length) (dcid, packet_number);
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v cid_len2))) (serialize_packet_number last2 pn_length) (dcid, packet_number);
    serialize_packet_number_ext last1 last2 pn_length packet_number
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last1 packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last2 packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MHandshake payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MZeroRTT payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last1 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last1 packet_number_length) (plpnl, packet_number);
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last2 packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last2 packet_number_length) (plpnl, packet_number);
      serialize_packet_number_ext last1 last2 packet_number_length packet_number
    | MRetry unused odcid ->
      assert_norm (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len1 last1 (MLong version dcid scid (MRetry unused odcid))) == (| Long, (| (), (| Retry, () |) |) |) );
      assert_norm (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header cid_len2 last2 (MLong version dcid scid (MRetry unused odcid))) == (| Long, (| (), (| Retry, () |) |) |) )
    end

#pop-options

(* Fulfill the interface *)

let last_packet_number
  (h: header)
: Tot last_packet_number_t
= if is_retry h then 0uL else let pn = packet_number h in if pn = 0uL then 0uL else pn `U64.sub` 1uL

#push-options "--z3rlimit 32"

let parse_header_prop_intro
  (h: header)
: Lemma
  (parse_header_prop (U32.uint_to_t (dcid_len h)) (last_packet_number h) h)
= ()

#pop-options

let format_header' (h: header) : GTot bytes =
  parse_header_prop_intro h;
  serialize (serialize_header (U32.uint_to_t (dcid_len h)) (last_packet_number h)) h

let header_len h =
  assert_norm (
    let k = parse_header_kind' (U32.uint_to_t (dcid_len h)) (last_packet_number h) in
    match k.parser_kind_high with
    | None -> False
    | Some hg -> hg < header_len_bound
  );
  parse_header_prop_intro h;
  Seq.length (format_header' h)

let format_header h = format_header' h

#push-options "--z3rlimit 32"

let format_header_is_short h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert (MShort? h <==> uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Short <: U8.t))

#pop-options

let first_byte_is_retry
  (k: bitsum'_type first_byte)
: GTot bool
= match k with
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) -> true
  | _ -> false

let first_byte_is_retry_correct
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (is_retry h <==> first_byte_is_retry (first_byte_of_header short_dcid_len last h))
= ()

let repr_of_pn_length
  (x: packet_number_length_t)
: Tot (y: enum_repr packet_number_length {
    list_mem x (list_map fst packet_number_length) /\
    y == enum_repr_of_key packet_number_length x
  })
= assert_norm (pow2 8 == 256);
  Cast.uint32_to_uint8 (x `U32.sub` 1ul)

#push-options "--z3rlimit 512 --max_fuel 8 --initial_fuel 8 --max_ifuel 8 --initial_ifuel 8"

#restart-solver

let format_header_is_retry h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert (is_retry h <==> (
    uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Long <: U8.t) /\
    uint8.get_bitfield (Seq.index (format_header h) 0) 4 6 == (LowParse.Spec.Enum.enum_repr_of_key long_packet_type Retry <: U8.t)
  ))

#restart-solver

let format_header_pn_length h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  let pnl_k = pn_length h in
  let pnl_r = repr_of_pn_length pnl_k in
  assert (list_mem pnl_k (list_map fst packet_number_length));
  assert (pnl_r == enum_repr_of_key packet_number_length pnl_k); 
  assert (
    uint8.get_bitfield (Seq.index (format_header h) 0) 0 2 ==
    (pnl_r <: U8.t)
  )

#pop-options

val pn_offset'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last )
: Ghost nat
  (requires (~ (is_retry h)))
  (ensures (fun n ->
    let s = serialize (serialize_header short_dcid_len last) h in
    0 < n /\
    n + U32.v (pn_length h) == Seq.length s /\
    S.slice s n (S.length s) `S.equal` serialize (serialize_packet_number last (pn_length h)) (packet_number h)
  ))

#push-options "--z3rlimit 1024 --query_stats --max_fuel 4 --initial_fuel 4"

#restart-solver

let pn_offset'
  short_dcid_len last h
= serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  match h with
  | MShort spin key_phase dcid packet_number_length packet_number ->
    assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) ) ;
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) (serialize_packet_number last packet_number_length) (dcid, packet_number);
    serialize_length (serialize_packet_number last packet_number_length) packet_number;
    1 + S.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) dcid)
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + S.length (serialize serialize_common_long (version, (dcid, scid))) + S.length (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) + S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    | MHandshake payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + S.length (serialize serialize_common_long (version, (dcid, scid))) + S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    | MZeroRTT payload_length packet_number_length packet_number ->
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      serialize_length (serialize_packet_number last packet_number_length) packet_number;
      1 + S.length (serialize serialize_common_long (version, (dcid, scid))) + S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl)
    end

#pop-options

let pn_offset h =
  pn_offset' (U32.uint_to_t (dcid_len h)) (last_packet_number h) h

(* From https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5.4.2 *)

let putative_pn_offset cid_len x =
  match parse parse_u8 x with
  | None -> None
  | Some (hd, consumed1) ->
    let _ =
      parser_kind_prop_equiv parse_u8_kind parse_u8;
      assert (consumed1 == 1) 
    in
    let x1 = Seq.slice x consumed1 (Seq.length x) in
    if uint8.get_bitfield hd 7 8 = 0uy // test packet kind
    then // short
      if not (cid_len <= 20)
      then None
      else
      match parse (parse_flbytes cid_len) x1 with
      | None -> None
      | Some (_, consumed2) ->
        Some (consumed1 + consumed2)
    else // long
      let packet_type = uint8.get_bitfield hd 4 6 in
      if packet_type = 3uy // is retry?
      then None
      else
        match parse parse_common_long x1 with
        | None -> None
        | Some (_, consumed2) ->
          let x2 = Seq.slice x1 consumed2 (Seq.length x1) in
          let mconsumed3 : option (consumed_length x2) =
            if packet_type = 0uy // is initial?
            then
              match parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x2 with
              | None -> None
              | Some (_, x3) -> Some x3
            else Some 0
          in
          match mconsumed3 with
          | None -> None
          | Some consumed3 ->
            match parse parse_varint (Seq.slice x2 consumed3 (Seq.length x2)) with
            | None -> None
            | Some (_, consumed4) -> Some (consumed1 + consumed2 + consumed3 + consumed4)

#push-options "--z3rlimit 512"

#restart-solver

let putative_pn_offset_frame
  cid_len x1 x2
= let Some off = putative_pn_offset cid_len x1 in
  parse_u8_spec' x1;
  parse_u8_spec' x2;
  parser_kind_prop_equiv parse_u8_kind parse_u8;
  let hd1 = Seq.index x1 0 in
  let is_short = uint8.get_bitfield hd1 7 8 = 0uy in
  let number_of_protected_bits = if is_short then 5 else 4 in
  let hd2 = Seq.index x2 0 in
  BF.get_bitfield_get_bitfield (U8.v hd1) number_of_protected_bits 8 (7 - number_of_protected_bits) (8 - number_of_protected_bits);
  BF.get_bitfield_get_bitfield (U8.v hd2) number_of_protected_bits 8 (7 - number_of_protected_bits) (8 - number_of_protected_bits);
  assert (uint8.get_bitfield hd1 7 8 == uint8.get_bitfield hd2 7 8);
  let x1_1 = Seq.slice x1 1 (Seq.length x1) in
  let x2_1 = Seq.slice x2 1 (Seq.length x2) in
  let x'1 = Seq.slice x1_1 0 (off - 1) in
  if is_short
  then begin
    parse_strong_prefix (parse_flbytes cid_len) x1_1 x'1;
    parse_strong_prefix (parse_flbytes cid_len) x'1 x2_1
  end else begin
    let packet_type = uint8.get_bitfield hd1 4 6 in
    BF.get_bitfield_get_bitfield (U8.v hd1) 4 8 0 2;
    BF.get_bitfield_get_bitfield (U8.v hd2) 4 8 0 2;
    assert (packet_type == uint8.get_bitfield hd2 4 6);
    parse_strong_prefix parse_common_long x1_1 (Seq.slice x1_1 0 (off - 1));
    parse_strong_prefix parse_common_long (Seq.slice x2_1 0 (off - 1)) x2_1;
    let Some (_, consumed2) = parse parse_common_long x1_1 in
    let x1_2 = Seq.slice x1_1 consumed2 (Seq.length x1_1) in
    let x2_2 = Seq.slice x2_1 consumed2 (Seq.length x2_1) in
    assert (Seq.slice (Seq.slice x1_1 0 (off - 1)) consumed2 (off - 1) == Seq.slice (Seq.slice x2_1 0 (off - 1)) consumed2 (off - 1));
    if packet_type = 0uy
    then begin
      let x'2 = Seq.slice x1_2 0 (off - 1 - consumed2) in
      parse_strong_prefix
        (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len))
        x1_2 x'2;
      parse_strong_prefix
        (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len))
        x'2 x2_2          
    end;
    let consumed3 =
      if packet_type = 0uy
      then let Some (_, consumed3) = parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x1_2 in consumed3
      else 0
    in
    let x1_3 = Seq.slice x1_2 consumed3 (Seq.length x1_2) in
    let x2_3 = Seq.slice x2_2 consumed3 (Seq.length x2_2) in
    assert (Seq.slice (Seq.slice x1_2 0 (off - 1 - consumed2)) consumed3 (off - 1 - consumed2) == Seq.slice (Seq.slice x2_2 0 (off - 1 - consumed2)) consumed3 (off - 1 - consumed2));
    let x'3 = Seq.slice x1_3 0 (off - 1 - consumed2 - consumed3) in
    parse_strong_prefix parse_varint x1_3 x'3;
    parse_strong_prefix parse_varint x'3 x2_3
  end

#pop-options

let putative_pn_offset_is_retry
  cid_len x
= parser_kind_prop_equiv parse_u8_kind parse_u8;
  if S.length x = 0
  then ()
  else parse_u8_spec' x

val format_header_is_initial: h: header -> Lemma
  ((MLong? h /\ MInitial? (MLong?.spec h))  <==> (
    BF.get_bitfield (U8.v (S.index (format_header h) 0)) 7 8 == 1 /\
    BF.get_bitfield (U8.v (S.index (format_header h) 0)) 4 6 == 0
  ))

#push-options "--z3rlimit 256 --max_fuel 8 --initial_fuel 8 --max_ifuel 8 --initial_ifuel 8"

#restart-solver

let format_header_is_initial h =
  parse_header_prop_intro h;
  let dl = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  serialize_header_eq dl last h;
  let tg = first_byte_of_header dl last h in
  let x = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec x;
  assert (Seq.index (format_header h) 0 == x);
  assert ((MLong? h /\ MInitial? (MLong?.spec h)) <==> (
    uint8.get_bitfield (Seq.index (format_header h) 0) 7 8 == (LowParse.Spec.Enum.enum_repr_of_key header_form Long <: U8.t) /\
    uint8.get_bitfield (Seq.index (format_header h) 0) 4 6 == (LowParse.Spec.Enum.enum_repr_of_key long_packet_type Initial <: U8.t)
  ))

#pop-options

#push-options "--z3rlimit 1024 --max_fuel 4 --initial_fuel 4 --query_stats"

#restart-solver

let putative_pn_offset_correct h cid_len =
  let x = format_header h in
  let short_dcid_len : short_dcid_len_t = U32.uint_to_t (dcid_len h) in
  let last : last_packet_number_t = last_packet_number h in
  parse_header_prop_intro h;
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let kt = bitsum'_key_of_t first_byte tg in
  let hd = synth_bitsum'_recip first_byte tg in
  LI.serialize_u8_spec hd;
  parse_serialize serialize_u8 hd;
  parse_strong_prefix parse_u8 (serialize serialize_u8 hd) (serialize serialize_u8 hd `S.append` serialize (serialize_header_body short_dcid_len last kt) (mk_header_body short_dcid_len last tg h));
  assert (parse parse_u8 x == Some (hd, 1));
  let x1 = S.slice x 1 (Seq.length x) in
  assert (x1 `S.equal` serialize (serialize_header_body short_dcid_len last kt) (mk_header_body short_dcid_len last tg h));
  format_header_is_short h;
  assert (MShort? h <==> uint8.get_bitfield hd 7 8 = 0uy);
  if uint8.get_bitfield hd 7 8 = 0uy
  then begin
    assert (MShort? h);
    assert (cid_len == dcid_len h);
    assert (cid_len <= 20);
    let MShort spin key_phase dcid packet_number_length packet_number = h in
    assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
    assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) );
//    assert (x1 == serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len) `serialize_nondep_then` serialize_packet_number last (MShort?.packet_number_length h)) (MShort?.dcid h, MShort?.packet_number h));
    serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (serialize_packet_number last (MShort?.packet_number_length h)) (MShort?.dcid h, MShort?.packet_number h);
    assert (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h) == serialize (serialize_flbytes cid_len) (MShort?.dcid h));
    parse_serialize (serialize_flbytes cid_len) (MShort?.dcid h);
    parse_strong_prefix (parse_flbytes cid_len) (serialize (serialize_flbytes cid_len) (MShort?.dcid h)) x1;
    assert (parse (parse_flbytes cid_len) x1 == Some (MShort?.dcid h, S.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h))));
    assert (putative_pn_offset cid_len x = Some (1 + S.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes cid_len)) (MShort?.dcid h))));
    assert_norm (pn_offset' short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == 1 + S.length (serialize (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) dcid));
    ()
  end else begin
    assert (MLong? h);
    let MLong version dcid scid spec = h in
    format_header_is_retry h;
    assert (is_retry h <==> uint8.get_bitfield hd 4 6 == 3uy);
    assert (~ (MRetry? spec));
    format_header_is_initial h;
    assert (MInitial? spec <==> uint8.get_bitfield hd 4 6 == 0uy);
    if uint8.get_bitfield hd 4 6 = 0uy
    then begin
      assert (MInitial? spec);
      let MInitial token payload_length packet_number_length packet_number = spec in
      assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
      let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
      serialize_nondep_then_eq serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (token, (plpnl, packet_number)));
      parse_serialize serialize_common_long (version, (dcid, scid));
      parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
      let consumed2 = S.length (serialize serialize_common_long (version, (dcid, scid))) in
      assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
      let x2 = S.slice x1 consumed2 (S.length x1) in
      assert (x2 `S.equal` serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number)));
      serialize_nondep_then_eq (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) (token, (plpnl, packet_number));
      parse_serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token;
      parse_strong_prefix (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) x2;
      let consumed3 = S.length (serialize (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) token) in
      assert (parse (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) x2 == Some (token, consumed3));
      let x3 = S.slice x2 consumed3 (S.length x2) in
      assert (x3 `S.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
      serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
      assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
      parse_serialize serialize_varint plpnl;
      parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
      let consumed4 = S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
      assert (consumed4 == S.length (serialize serialize_varint plpnl));
      assert (parse parse_varint x3 == Some (plpnl, consumed4));
      assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed3 + consumed4));
      assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == 1 + consumed2 + consumed3 + consumed4)
    end else
      match spec with
      | MHandshake payload_length packet_number_length packet_number ->
        assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
        assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
        let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
        serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
        parse_serialize serialize_common_long (version, (dcid, scid));
        parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
        let consumed2 = S.length (serialize serialize_common_long (version, (dcid, scid))) in
        assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
        let x2 = S.slice x1 consumed2 (S.length x1) in
        assert (x2 `S.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
        let x3 = S.slice x2 0 (S.length x2) in
        assert (x3 `S.equal` x2);
        serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
        assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
        parse_serialize serialize_varint plpnl;
        parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
        let consumed4 = S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
        assert (consumed4 == S.length (serialize serialize_varint plpnl));
        assert (parse parse_varint x3 == Some (plpnl, consumed4));
        assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed4));
        assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == 1 + consumed2 + 0 + consumed4)
      | MZeroRTT payload_length packet_number_length packet_number ->
        assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
        assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
        let plpnl : (plpnl : uint62_t { payload_and_pn_length_prop packet_number_length plpnl }) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
        serialize_nondep_then_eq serialize_common_long (serialize_payload_length_pn last packet_number_length) ((version, (dcid, scid)), (plpnl, packet_number));
        parse_serialize serialize_common_long (version, (dcid, scid));
        parse_strong_prefix parse_common_long (serialize serialize_common_long (version, (dcid, scid))) x1;
        let consumed2 = S.length (serialize serialize_common_long (version, (dcid, scid))) in
        assert (parse parse_common_long x1 == Some ((version, (dcid, scid)), consumed2));
        let x2 = S.slice x1 consumed2 (S.length x1) in
        assert (x2 `S.equal` serialize (serialize_payload_length_pn last packet_number_length) (plpnl, packet_number));
        let x3 = S.slice x2 0 (S.length x2) in
        assert (x3 `S.equal` x2);
        serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) (serialize_packet_number last packet_number_length) (plpnl, packet_number);
        assert (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl == serialize serialize_varint plpnl);
        parse_serialize serialize_varint plpnl;
        parse_strong_prefix parse_varint (serialize serialize_varint plpnl) x3;
        let consumed4 = S.length (serialize (serialize_varint `serialize_filter` payload_and_pn_length_prop packet_number_length) plpnl) in
        assert (consumed4 == S.length (serialize serialize_varint plpnl));
        assert (parse parse_varint x3 == Some (plpnl, consumed4));
        assert (putative_pn_offset cid_len x = Some (1 + consumed2 + consumed4));
        assert_norm (pn_offset' short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == 1 + consumed2 + 0 + consumed4)
  end

#pop-options

let parse_header cid_len last b =
  match parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

module Seq = FStar.Seq

let lemma_header_parsing_correct
  h c cid_len last
=
  parse_header_prop_intro h;
  let cid_len32 : short_dcid_len_t = U32.uint_to_t cid_len in
  serialize_header_ext (U32.uint_to_t (dcid_len h)) cid_len32 (last_packet_number h) (U64.uint_to_t last) h;
  let s = format_header h in
  assert (s == serialize (serialize_header cid_len32 (U64.uint_to_t last)) h);
  parse_serialize (serialize_header cid_len32 (U64.uint_to_t last)) h;
  assert_norm ((parse_header_kind' cid_len32 (U64.uint_to_t last)).parser_kind_subkind == Some ParserStrong);
  parse_strong_prefix (lp_parse_header cid_len32 (U64.uint_to_t last)) s (s `Seq.append` c);
  S.lemma_split (s `S.append` c) (S.length s);
  assert (s `S.equal` S.slice s 0 (S.length s));
  match parse_header cid_len last Seq.(format_header h @| c) with
  | H_Failure -> ()
  | H_Success h' c' -> assert (h == h'); assert (c `Seq.equal` c')

#push-options "--z3rlimit 256"

let lemma_header_parsing_safe
  cid_len last b1 b2
= match parse_header cid_len last b1 with
  | H_Failure -> ()
  | H_Success h1 c1 ->
    let consumed = Seq.length b1 - Seq.length c1 in
    assert (Some? (parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1)); //  == Some (h1, consumed));
    let Some (h1', consumed') = parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 in
    assert (h1 == h1');
    let consumed' : consumed_length b1 = consumed' in
    assert (consumed' <= Seq.length b1);
    assert (c1 == Seq.slice b1 consumed' (Seq.length b1));
    assert (consumed == consumed');
    parse_injective (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b1 b2;
    Seq.lemma_split b1 consumed;
    assert (parse_header cid_len last b2 == H_Success h1 c1);
    Seq.lemma_split b2 consumed;
    assert (b1 == b2)
    
#pop-options

let header_len'
  (h: header)
: GTot nat
= match h with
  | MShort spin phase cid packet_number_length pn ->
    1 + FB.length cid + U32.v packet_number_length
  | MLong version dcid scid spec ->
    7 + FB.length dcid + FB.length scid +
    begin match spec with
    | MInitial token payload_length packet_number_length pn ->
      S.length (serialize (serialize_bounded_varint 0 token_max_len) (FB.len token)) + FB.length token + S.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MZeroRTT payload_length packet_number_length pn ->
      S.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MHandshake payload_length packet_number_length pn ->
      S.length (serialize serialize_varint (payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length)) + U32.v packet_number_length
    | MRetry unused odcid ->
      1 + FB.length odcid
    end

let length_serialize_common_long
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
: Lemma
  (Seq.length (serialize serialize_common_long (version, (dcid, scid))) == 6 + FB.length dcid + FB.length scid)
= serialize_nondep_then_eq serialize_u32 (serialize_bounded_vlbytes 0 20 `serialize_nondep_then` serialize_bounded_vlbytes 0 20) (version, (dcid, scid));
  serialize_length serialize_u32 version;
  serialize_nondep_then_eq (serialize_bounded_vlbytes 0 20) (serialize_bounded_vlbytes 0 20) (dcid, scid);
  length_serialize_bounded_vlbytes 0 20 dcid;
  length_serialize_bounded_vlbytes 0 20 scid

let length_serialize_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
  (payload_and_pn_length: parse_filter_refine (payload_and_pn_length_prop pn_length))
  (pn: packet_number_t last pn_length)
: Lemma
  (Seq.length (serialize (serialize_payload_length_pn last pn_length) (payload_and_pn_length, pn)) == Seq.length (serialize serialize_varint payload_and_pn_length) + U32.v pn_length)
= serialize_nondep_then_eq (serialize_varint `serialize_filter` payload_and_pn_length_prop pn_length) (serialize_packet_number last pn_length) (payload_and_pn_length, pn);
  serialize_length (serialize_packet_number last pn_length) pn

#push-options "--z3rlimit 1024 --query_stats --max_fuel 4 --initial_fuel 4"

#restart-solver

let header_len'_correct'_short
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (spin: bool)
  (key_phase: bool)
  (dcid: vlbytes 0 20)
  (packet_number_length: packet_number_length_t)
  (packet_number: uint62_t)
: Lemma
  (requires (let h = MShort spin key_phase dcid packet_number_length packet_number in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MShort spin key_phase dcid packet_number_length packet_number in
    header_len' h == S.length (serialize (serialize_header short_dcid_len last) h)
  ))
= 
  let h = MShort spin key_phase dcid packet_number_length packet_number in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  assert_norm (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number) == (| Short, (| (), ((if spin then 1uy else 0uy), (| (), ((if key_phase then 1uy else 0uy), (| packet_number_length, () |) ) |) ) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MShort spin key_phase dcid packet_number_length packet_number)) == (| Short, (| (), (| (), (| packet_number_length, () |) |) |) |) ) ;
  serialize_nondep_then_eq (serialize_weaken (strong_parser_kind 0 20 None) (serialize_flbytes (U32.v short_dcid_len))) (serialize_packet_number last packet_number_length) (dcid, packet_number);
  serialize_length (serialize_flbytes (U32.v short_dcid_len)) dcid;
  serialize_length (serialize_packet_number last packet_number_length) packet_number

#restart-solver

let header_len'_correct'_long_initial
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (token: vlbytes 0 token_max_len)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
    header_len' h == S.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MInitial token payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number)) == (| Long, (| (), (| Initial, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MInitial token payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) `serialize_nondep_then` serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (token, (plpnl, pn));
  length_serialize_common_long version dcid scid;
  length_serialize_nondep_then (serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len)) (serialize_payload_length_pn last packet_number_length) token (plpnl, pn);
  length_serialize_bounded_vlgenbytes 0 token_max_len (serialize_bounded_varint 0 token_max_len) token;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_handshake
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
    header_len' h == S.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MHandshake payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number)) == (| Long, (| (), (| Handshake, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MHandshake payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (plpnl, pn);
  length_serialize_common_long version dcid scid;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_zeroRTT
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (payload_length: uint62_t)
  (packet_number_length: packet_number_length_t { U64.v payload_length + U32.v packet_number_length < pow2 62 })
  (packet_number: uint62_t)
: Lemma
  (requires (
    let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
    header_len' h == S.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number)) == (| Long, (| (), (| ZeroRTT, (| (), (| packet_number_length, () |) |) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MZeroRTT payload_length packet_number_length packet_number))) == kt );
  let plpnl : parse_filter_refine (payload_and_pn_length_prop packet_number_length) = payload_length `U64.add` Cast.uint32_to_uint64 packet_number_length in
  let pn : packet_number_t last packet_number_length = packet_number in
  length_serialize_nondep_then serialize_common_long (serialize_payload_length_pn last packet_number_length) (version, (dcid, scid)) (plpnl, pn);
  length_serialize_common_long version dcid scid;
  length_serialize_payload_length_pn last packet_number_length plpnl pn

let header_len'_correct'_long_retry
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (version: U32.t)
  (dcid: vlbytes 0 20)
  (scid: vlbytes 0 20)
  (unused: bitfield 4)
  (odcid: vlbytes 0 20)
: Lemma
  (requires (
    let h = MLong version dcid scid (MRetry unused odcid) in
    parse_header_prop short_dcid_len last h
  ))
  (ensures (
    let h = MLong version dcid scid (MRetry unused odcid) in
    header_len' h == S.length (serialize (serialize_header short_dcid_len last) h)
  ))
=
  let h = MLong version dcid scid (MRetry unused odcid) in
  serialize_header_eq short_dcid_len last h;
  let tg = first_byte_of_header short_dcid_len last h in
  let x = synth_bitsum'_recip first_byte tg in
  serialize_length LI.serialize_u8 x;
  let kt : bitsum'_key_type first_byte = (| Long, (| (), (| Retry, () |) |) |) in
  assert_norm (first_byte_of_header short_dcid_len last (MLong version dcid scid (MRetry unused odcid)) == (| Long, (| (), (| Retry, (unused, ()) |) |) |) );
  assert_norm (bitsum'_key_of_t first_byte (first_byte_of_header short_dcid_len last (MLong version dcid scid (MRetry unused odcid))) == kt );
  length_serialize_nondep_then serialize_common_long (serialize_bounded_vlbytes 0 20) (version, (dcid, scid)) odcid;
  length_serialize_common_long version dcid scid;
  length_serialize_bounded_vlbytes 0 20 odcid

let header_len'_correct'
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (h: header' short_dcid_len last)
: Lemma
  (header_len' h == S.length (serialize (serialize_header short_dcid_len last) h))
= match h with
  | MShort spin key_phase dcid packet_number_length packet_number ->
    header_len'_correct'_short short_dcid_len last spin key_phase dcid packet_number_length packet_number
  | MLong version dcid scid spec ->
    begin match spec with
    | MInitial token payload_length packet_number_length packet_number ->
      header_len'_correct'_long_initial short_dcid_len last version dcid scid token payload_length packet_number_length packet_number
    | MHandshake payload_length packet_number_length packet_number ->
      header_len'_correct'_long_handshake short_dcid_len last version dcid scid payload_length packet_number_length packet_number
    | MZeroRTT payload_length packet_number_length packet_number ->
      header_len'_correct'_long_zeroRTT short_dcid_len last version dcid scid payload_length packet_number_length packet_number
    | MRetry unused odcid ->
      header_len'_correct'_long_retry short_dcid_len last version dcid scid unused odcid
    end

#pop-options

let header_len'_correct
  (h: header)
: Lemma
  (header_len' h == header_len h)
= 
  let short_dcid_len = U32.uint_to_t (dcid_len h) in
  let last = last_packet_number h in
  header_len'_correct' short_dcid_len last h
