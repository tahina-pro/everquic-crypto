module QUIC.Parse
open QUIC.Spec.Base
open QUIC.Parse.PacketNumber

open FStar.HyperStack.ST

open LowParse.Spec.Int
open LowParse.Spec.BitSum

open LowParse.Spec.BoundedInt

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

(* From https://tools.ietf.org/html/draft-ietf-quic-transport-23#section-17 *)

inline_for_extraction
noextract
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
noextract
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

// TODO: replace the payload_length type with a refinement (payload_and_pn_length: uint62_t { U64.v payload_and_pn_length >= U32.v pn_length }), and replace the parser with the corresponding (parse_filter parse_varint); then add the conversions from payload_and_pn_length to payload_length and back in mk_header and mk_body

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot Type0
= (uint62_t & packet_number_t last pn_length)

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
    | ((version, (dcid, scid)), (token, (payload_length, packet_number))) ->
      MLong version dcid scid (MInitial token payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MZeroRTT payload_length pn_length packet_number)
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match coerce (common_long_t & payload_length_pn last pn_length) pl with
    | ((version, (dcid, scid)), (payload_length, packet_number)) ->
      MLong version dcid scid (MHandshake payload_length pn_length packet_number)
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
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (token, (payload_length, packet_number))) <: (common_long_t & (parse_bounded_vlbytes_t 0 token_max_len & payload_length_pn last pn_length)))
    end
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MZeroRTT payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MHandshake payload_length _ packet_number) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), (payload_length, packet_number)) <: (common_long_t & payload_length_pn last pn_length))
    end
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    begin match pl with
    | MLong version dcid scid (MRetry unused odcid) ->
      coerce (header_body_type short_dcid_len last (bitsum'_key_of_t first_byte k')) (((version, (dcid, scid)), odcid) <: (common_long_t & parse_bounded_vlbytes_t 0 20))
    end

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

open QUIC.Parse.VarInt

let parse_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (parser _ (payload_length_pn last pn_length))
= parse_varint `nondep_then` parse_packet_number last pn_length

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
= serialize_varint `serialize_nondep_then` serialize_packet_number last pn_length

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

module LC = LowParse.Low.Combinators
module LB = LowParse.Low.Bytes
module LI = LowParse.Low.BoundedInt
module LJ = LowParse.Low.Int
module LL = LowParse.Low.BitSum

inline_for_extraction
let validate_common_long : LC.validator parse_common_long =
  LB.validate_u32 () `LC.validate_nondep_then` (LB.validate_bounded_vlbytes 0 20 `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20)

inline_for_extraction
noextract
let validate_payload_length_pn
  (last: last_packet_number_t)
  (pn_length: packet_number_length_t)
: Tot (LC.validator (parse_payload_length_pn last pn_length))
= validate_varint `LC.validate_nondep_then` validate_packet_number last pn_length

[@filter_bitsum'_t_attr]
inline_for_extraction
noextract
let validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
  (k' : bitsum'_key_type first_byte)
: Tot (LC.validator (dsnd (parse_header_body short_dcid_len last k')))
= match coerce (bitsum'_key_type first_byte) k' with
  | (| Short, (| (), (| (), (| pn_length, () |) |) |) |) ->
    LC.validate_weaken (strong_parser_kind 0 20 None) (LB.validate_flbytes (U32.v short_dcid_len) short_dcid_len) () `LC.validate_nondep_then` validate_packet_number last pn_length
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` (LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) `LC.validate_nondep_then` validate_payload_length_pn last pn_length)
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    validate_common_long `LC.validate_nondep_then` validate_payload_length_pn last pn_length
  | (| Long, (| (), (| Retry, () |) |) |) ->
    validate_common_long `LC.validate_nondep_then` LB.validate_bounded_vlbytes 0 20

let filter_first_byte'
: (filter_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_filter_bitsum'_t' first_byte)

inline_for_extraction
let filter_first_byte
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (filter_bitsum'_t first_byte)
= coerce (filter_bitsum'_t first_byte) filter_first_byte'

inline_for_extraction
noextract
let mk_validate_header_body_cases'
: LL.validate_bitsum_cases_t first_byte
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (LL.mk_validate_bitsum_cases_t' first_byte)

inline_for_extraction
noextract
let mk_validate_header_body_cases
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: LL.validate_bitsum_cases_t first_byte
= coerce (LL.validate_bitsum_cases_t first_byte) mk_validate_header_body_cases' 

let validate_header
  (short_dcid_len: short_dcid_len_t)
  (last: last_packet_number_t)
: Tot (LL.validator (lp_parse_header short_dcid_len last))
= LL.validate_bitsum
    first_byte
    (first_byte_of_header short_dcid_len last)
    (header_body_type short_dcid_len last)
    (header_synth short_dcid_len last)
    (LJ.validate_u8 ())
    LJ.read_u8
    (filter_first_byte short_dcid_len last)
    (parse_header_body short_dcid_len last)
    (validate_header_body_cases short_dcid_len last)
    (mk_validate_header_body_cases short_dcid_len last)

#pop-options

(* Properties of the serializer *)

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
= admit ()

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

let format_header_is_retry h = admit ()

let format_header_pn_length h = admit ()

let pn_offset h = admit ()

(* From https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5.4.2 *)

let putative_pn_offset cid_len x =
  if not (1 <= cid_len && cid_len <= 4)
  then None
  else
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
      match parse (parse_bounded_integer cid_len) x1 with
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

let putative_pn_offset_frame cid_len x1 x2 = admit ()

let putative_pn_offset_correct h cid_len = admit ()

let parse_header cid_len last b =
  match parse (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) b with
  | None -> H_Failure
  | Some (h, consumed) -> H_Success h (Seq.slice b consumed (Seq.length b))

module Seq = FStar.Seq

#push-options "--z3rlimit 128"

let lemma_header_parsing_correct
  h c cid_len last
=
  parse_header_prop_intro h;
  serialize_header_ext (U32.uint_to_t (dcid_len h)) (U32.uint_to_t cid_len) (last_packet_number h) (U64.uint_to_t last) h;
  let s = format_header h in
  assert (s == serialize (serialize_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) h);
  parse_serialize (serialize_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) h;
  assert_norm ((parse_header_kind' (U32.uint_to_t cid_len) (U64.uint_to_t last)).parser_kind_subkind == Some ParserStrong);
  parse_strong_prefix (lp_parse_header (U32.uint_to_t cid_len) (U64.uint_to_t last)) s (s `Seq.append` c);
  match parse_header cid_len last Seq.(format_header h @| c) with
  | H_Failure -> ()
  | H_Success h' c' -> assert (h == h' /\ c `Seq.equal` c')

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

module Impl = QUIC.Impl.Base

inline_for_extraction
noextract
let destr_first_byte
: (destr_bitsum'_t first_byte)
= norm [primops; iota; zeta; delta_attr [`%filter_bitsum'_t_attr]]
  (mk_destr_bitsum'_t first_byte)

inline_for_extraction
noextract
let read_header_body_t
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (Type u#0)
= (len: U32.t) ->
  HST.Stack Impl.header
  (requires (fun h ->
    let p = dsnd (parse_header_body cid_len last (bitsum'_key_of_t first_byte tg)) in
    LL.valid_pos (lp_parse_header cid_len last) h sl 0ul len /\
    1 <= U32.v sl.LL.len /\
    LL.valid_pos p h sl 1ul len /\
    LL.contents (lp_parse_header cid_len last) h sl 0ul == (header_synth cid_len last).f tg (LL.contents p h sl 1ul)
  ))
  (ensures (fun h x h' ->
    B.modifies B.loc_none h h' /\
    begin
      let hd = LL.contents (lp_parse_header cid_len last) h sl 0ul in
      Impl.header_live x h' /\
      LL.loc_slice_from_to sl 0ul len `B.loc_includes` Impl.header_footprint x /\
      Impl.g_header x h' == hd
    end
  ))

#push-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

let read_header_body_short
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (spin: BF.bitfield uint8 1)
  (key_phase: BF.bitfield uint8 1)
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) == (| Short, (| (), (| (), (| pn_length, () |) |) |) |) );
    LL.valid_nondep_then h0 (weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len))) (parse_packet_number last pn_length) sl 1ul;
    LL.valid_weaken (strong_parser_kind 0 20 None) (parse_flbytes (U32.v cid_len)) h0 sl 1ul;
    LB.valid_flbytes_elim h0 (U32.v cid_len) sl 1ul;
    let pos = LB.jump_flbytes (U32.v cid_len) cid_len sl 1ul in
    let dcid = B.sub sl.LL.base 1ul (pos `U32.sub` 1ul) in
    let pn = read_packet_number last pn_length sl pos in
    Impl.BShort (spin = 1uy) (key_phase = 1uy) dcid cid_len pn pn_length

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_retry
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (unused: BF.bitfield uint8 4)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Retry, (unused, ()) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Retry, (unused, ()) |) |) |)  == (| Long, (| (), (| Retry, () |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlbytes 0 20) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    let odcid = LB.get_vlbytes_contents 0 20 sl pos3 in
    let odcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos3 in
    let spec = Impl.BRetry unused odcid odcid_len in
    Impl.BLong version dcid dcid_len scid scid_len spec

#pop-options

#push-options "--z3rlimit 512 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_initial
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len) `nondep_then` parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) (parse_payload_length_pn last pn_length) sl pos3;
    let token = LB.get_bounded_vlgenbytes_contents 0 token_max_len (read_bounded_varint 0 token_max_len) (jump_bounded_varint 0 token_max_len) sl pos3 in
    let token_len = LB.bounded_vlgenbytes_payload_length 0 token_max_len (read_bounded_varint 0 token_max_len) sl pos3 in
    let pos4 = LB.jump_bounded_vlgenbytes 0 token_max_len (jump_bounded_varint 0 token_max_len) (read_bounded_varint 0 token_max_len) sl pos3 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos4;
    let payload_length = read_varint sl pos4 in
    let pos5 = jump_varint sl pos4 in
    let pn = read_packet_number last pn_length sl pos5 in
//    assert (LL.loc_slice_from_to sl 0ul len `B.loc_includes` B.loc_buffer token);
    let spec = Impl.BInitial payload_length pn pn_length token token_len in
    Impl.BLong version dcid dcid_len scid scid_len spec

#pop-options

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats --max_fuel 9 --initial_fuel 9 --max_ifuel 9 --initial_ifuel 9 --query_stats"

#restart-solver

let read_header_body_long_handshake
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos3;
    let payload_length = read_varint sl pos3 in
    let pos4 = jump_varint sl pos3 in
    let pn = read_packet_number last pn_length sl pos4 in
    let spec = Impl.BHandshake payload_length pn pn_length in
    Impl.BLong version dcid dcid_len scid scid_len spec

#restart-solver

let read_header_body_long_ZeroRTT
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (pn_length: packet_number_length_t)
: Tot (read_header_body_t sl cid_len last (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) )
= fun len ->
    let h0 = HST.get () in
    assert_norm (bitsum'_key_of_t first_byte (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) == (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) );
    LL.valid_nondep_then h0 parse_common_long (parse_payload_length_pn last pn_length) sl 1ul;
    LL.valid_nondep_then h0 parse_u32 (parse_bounded_vlbytes 0 20 `nondep_then` parse_bounded_vlbytes 0 20) sl 1ul;
    let version = LJ.read_u32 sl 1ul in
    let pos1 = LJ.jump_u32 sl 1ul in
    LL.valid_nondep_then h0 (parse_bounded_vlbytes 0 20) (parse_bounded_vlbytes 0 20) sl pos1;
    let dcid = LB.get_vlbytes_contents 0 20 sl pos1 in
    let dcid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos1 in
    let pos2 = LB.jump_bounded_vlbytes 0 20 sl pos1 in
    let scid = LB.get_vlbytes_contents 0 20 sl pos2 in
    let scid_len = LB.bounded_vlbytes_payload_length 0 20 sl pos2 in
    let pos3 = LB.jump_bounded_vlbytes 0 20 sl pos2 in
    LL.valid_nondep_then h0 parse_varint (parse_packet_number last pn_length) sl pos3;
    let payload_length = read_varint sl pos3 in
    let pos4 = jump_varint sl pos3 in
    let pn = read_packet_number last pn_length sl pos4 in
    let spec = Impl.BZeroRTT payload_length pn pn_length in
    Impl.BLong version dcid dcid_len scid scid_len spec

inline_for_extraction
noextract
let read_header_body
  (sl: LL.slice (B.trivial_preorder _) (B.trivial_preorder _))
  (cid_len: U32.t { U32.v cid_len < 20 } )
  (last: uint62_t { U64.v last + 1 < pow2 62 })
  (tg: bitsum'_type first_byte)
: Tot (read_header_body_t sl cid_len last tg)
= fun len ->
  let h0 = HST.get () in
  match tg with
  | (| Short, (| (), (spin, (| (), (key_phase, (| pn_length, () |) ) |) ) |) |) ->
    read_header_body_short sl cid_len last spin key_phase pn_length len
  | (| Long, (| (), (| Retry, (unused, ()) |) |) |) ->
    read_header_body_long_retry sl cid_len last unused len
  | (| Long, (| (), (| Initial, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_initial sl cid_len last pn_length len
  | (| Long, (| (), (| Handshake, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_handshake sl cid_len last pn_length len
  | (| Long, (| (), (| ZeroRTT, (| (), (| pn_length, () |) |) |) |) |) ->
    read_header_body_long_ZeroRTT sl cid_len last pn_length len

#pop-options

#restart-solver

#push-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --using_facts_from '*,-FStar.Int.Cast' --query_stats"

let read_header
  packet packet_len cid_len last
=
  let h0 = HST.get () in
  let sl = LL.make_slice packet packet_len in
  LL.valid_facts (lp_parse_header cid_len last) h0 sl 0ul;
  assert (B.as_seq h0 packet `Seq.equal` LL.bytes_of_slice_from h0 sl 0ul);
  let len = validate_header cid_len last sl 0ul in
  if len `U32.gt` LL.validator_max_length
  then None
  else begin
    let g = Ghost.hide (LL.contents (lp_parse_header cid_len last) h0 sl 0ul) in
    LL.valid_bitsum_elim
      #parse_u8_kind
      #8
      #U8.t
      #uint8
      first_byte
      #(header' cid_len last)
      (first_byte_of_header cid_len last)
      (header_body_type cid_len last)
      (header_synth cid_len last)
      parse_u8
      (parse_header_body cid_len last)
      h0
      sl
      0ul;
    let r = LJ.read_u8 sl 0ul in
    let res = destr_first_byte
      (read_header_body_t sl cid_len last)
      (fun _ cond dt df len' -> if cond then dt () len' else df () len')
      (read_header_body sl cid_len last)
      r
      len
    in
    lemma_header_parsing_post (U32.v cid_len) (U64.v last) (LL.bytes_of_slice_from h0 sl 0ul);
    Some (res, len)
  end

let impl_header_length
  x
=
  admit ()

let write_header
  dst x
=
  admit ()

let impl_putative_pn_offset
  cid_len b len
=
  let sl = LowParse.Slice.make_slice b len in
  let h0 = HST.get () in
  if not (1ul `U32.lte` cid_len && cid_len `U32.lte` 4ul)
  then 0ul
  else
    let _ = LL.valid_facts parse_u8 h0 sl 0ul in
    let pos1 = LJ.validate_u8 () sl 0ul in
    if pos1 `U32.gt` LL.validator_max_length
    then 0ul
    else
      let _ =
        parser_kind_prop_equiv parse_u8_kind parse_u8;
        assert (pos1 == 1ul)
      in
      let hd = LJ.read_u8 sl 0ul in
      if uint8.get_bitfield hd 7 8 = 0uy
      then
        let _ = LL.valid_facts (parse_bounded_integer (U32.v cid_len)) h0 sl pos1 in
        let pos2 = LI.validate_bounded_integer' cid_len sl pos1 in
        if pos2 `U32.gt` LL.validator_max_length
        then 0ul
        else pos2
      else
        let packet_type = uint8.get_bitfield hd 4 6 in
        if packet_type = 3uy
        then 0ul
        else
          let _ = LL.valid_facts parse_common_long h0 sl pos1 in
          let pos2 = validate_common_long sl pos1 in
          if pos2 `U32.gt` LL.validator_max_length
          then 0ul
          else
            let pos3 =
              if packet_type = 0uy
              then
                let _ = LL.valid_facts (parse_bounded_vlgenbytes 0 token_max_len (parse_bounded_varint 0 token_max_len)) h0 sl pos2 in
                let pos3 = LB.validate_bounded_vlgenbytes 0 0ul token_max_len (U32.uint_to_t token_max_len) (validate_bounded_varint 0ul (U32.uint_to_t token_max_len)) (read_bounded_varint 0 token_max_len) sl pos2 in
                if pos3 `U32.gt` LL.validator_max_length
                then 0ul
                else pos3
              else
                pos2
            in
            if pos3 = 0ul
            then 0ul
            else
              let _ = LL.valid_facts parse_varint h0 sl pos3 in
              let pos4 = validate_varint sl pos3 in
              if pos4 `U32.gt` LL.validator_max_length
              then 0ul
              else pos4

let impl_pn_offset
  h
= admit ()

let impl_header_len
  h
= admit ()

#pop-options
