module QUIC.Impl.Base
open QUIC.Spec.Base

module SecretIntegers = Lib.IntTypes
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module Spec = QUIC.Spec.Base

/// Information stored in a QUIC header. This is a Low* type passed by value --
/// it's a little expensive. Consider passing it by reference in ``encrypt``?
///
/// Note that we try to follow the convention of buffer arguments followed by
/// their lengths.

(* NOTE: in the following header type, payload_length contains the
length of the actual payload AND including the length of the packet
number. *)

(* NOTE: the header no longer contains the packet number, which is
part of the state, so that the client no longer needs to take care of
it *)

inline_for_extraction
noextract
type packet_number_length_t : Type0 = (x: SecretIntegers.uint32 { 1 <= SecretIntegers.v x /\ SecretIntegers.v x <= 4 })

noeq type long_header_specifics =
  | BInitial:
    payload_and_packet_number_length: uint62_t ->
    (packet_number_length: packet_number_length_t { SecretIntegers.v packet_number_length <= U64.v payload_and_packet_number_length /\ U64.v payload_and_packet_number_length < pow2 62 }) ->
    token: B.buffer U8.t -> (* I reordered those so that the extracted code for this type is a tagged union with common prefixes *)
    token_length: U32.t { let v = U32.v token_length in v == B.length token /\ 0 <= v /\ v <= token_max_len  } ->
    long_header_specifics
  | BZeroRTT:
    payload_and_packet_number_length: uint62_t ->
    (packet_number_length: packet_number_length_t { SecretIntegers.v packet_number_length <= U64.v payload_and_packet_number_length /\ U64.v payload_and_packet_number_length < pow2 62 }) ->
    long_header_specifics
  | BHandshake:
    payload_and_packet_number_length: uint62_t ->
    (packet_number_length: packet_number_length_t { SecretIntegers.v packet_number_length <= U64.v payload_and_packet_number_length /\ U64.v payload_and_packet_number_length < pow2 62 }) ->
    long_header_specifics
  | BRetry:
    unused: bitfield 4 ->
    odcid: B.buffer U8.t ->
    odcil: U32.t { let v = U32.v odcil in v = B.length odcid /\ 0 <= v /\ v <= 20 } ->
    long_header_specifics

noeq type header =
  | BLong:
    version: U32.t ->
    dcid: B.buffer U8.t ->
    dcil: U32.t { let v = U32.v dcil in v == B.length dcid /\ 0 <= v /\ v <= 20 } ->
    scid: B.buffer U8.t ->
    scil: U32.t { let v = U32.v scil in v == B.length scid /\ 0 <= v /\ v <= 20 } ->
    spec: long_header_specifics ->
    header
  | BShort:
    spin: bool ->
    phase: bool ->
    cid: B.buffer U8.t ->
    cid_len: U32.t{
      let l = U32.v cid_len in
      l == B.length cid /\
      0 <= l /\ l <= 20
    } ->
    packet_number_length: packet_number_length_t ->
    header

let dcid_len
  (h: header)
: Tot U32.t
= match h with
  | BShort spin phase cid cid_len packet_number_length ->
    cid_len
  | BLong version dcid dcil scid scil spec -> dcil

// inline_for_extraction
let is_retry
  (h: header)
: Tot bool
= BLong? h && BRetry? (BLong?.spec h)

// inline_for_extraction
let pn_length
  (h: header {~ (is_retry h)})
: Tot packet_number_length_t
= match h with
  | BShort spin phase cid cid_len packet_number_length ->
    packet_number_length
  | BLong version dcid dcil scid scil spec ->
    begin match spec with
    | BInitial payload_length packet_number_length token token_length ->
      packet_number_length
    | BZeroRTT payload_length packet_number_length ->
      packet_number_length
    | BHandshake payload_length packet_number_length ->
      packet_number_length
    end

// inline_for_extraction
let has_payload_length
  (h: header)
: Tot bool
= BLong? h && not (BRetry? (BLong?.spec h))

inline_for_extraction
let suint62_t = (x: SecretIntegers.uint64 { SecretIntegers.v x < U64.v uint62_bound })

// inline_for_extraction
let payload_length
  (h: header { has_payload_length h })
: Tot suint62_t
= match BLong?.spec h with
  | BInitial pl pnl _ _ -> SecretIntegers.to_u64 pl `SecretIntegers.sub` SecretIntegers.to_u64 pnl
  | BZeroRTT pl pnl -> SecretIntegers.to_u64 pl `SecretIntegers.sub` SecretIntegers.to_u64 pnl
  | BHandshake pl pnl -> SecretIntegers.to_u64 pl `SecretIntegers.sub` SecretIntegers.to_u64 pnl

module HS = FStar.HyperStack

let header_live (h: header) (m: HS.mem) : GTot Type0 =
  match h with
  | BShort spin phase cid cid_len packet_number_length ->
    B.live m cid
  | BLong version dcid dcil scid scil spec ->
    B.live m dcid /\ B.live m scid /\
    begin match spec with
    | BInitial payload_length packet_number_length token token_length ->
      B.live m token
    | BRetry unused odcid odcil ->
      B.live m odcid
    | _ -> True
    end

let header_footprint (h: header) : GTot B.loc =
  match h with
  | BShort spin phase cid cid_len packet_number_length ->
    B.loc_buffer cid
  | BLong version dcid dcil scid scil spec ->
    (B.loc_buffer dcid `B.loc_union` B.loc_buffer scid) `B.loc_union`
    begin match spec with
    | BInitial payload_length packet_number_length token token_length ->
      B.loc_buffer token
    | BRetry unused odcid odcil ->
      B.loc_buffer odcid
    | _ -> B.loc_none
    end

let header_live_loc_not_unused_in_footprint (h: header) (m: HS.mem) : Lemma
  (requires (header_live h m))
  (ensures (B.loc_not_unused_in m `B.loc_includes` header_footprint h))
= ()

module FB = FStar.Bytes

let u32_of_su32 (x: SecretIntegers.uint32) : GTot U32.t =
  U32.uint_to_t (SecretIntegers.v x)

let pnl_of_spnl (pnl: packet_number_length_t) : GTot Spec.packet_number_length_t =
  u32_of_su32 pnl

let u64_of_su64 (x: SecretIntegers.uint64) : GTot U64.t =
  U64.uint_to_t (SecretIntegers.v x)

let u62_of_su62 (x: suint62_t) : GTot uint62_t =
  u64_of_su64 x

#push-options "--z3rlimit 16"

let g_header (h: header) (m: HS.mem) (packet_number: uint62_t) : GTot Spec.header =
  match h with
  | BShort spin phase cid cid_len packet_number_length ->
    MShort spin phase (FB.hide (B.as_seq m cid)) (pnl_of_spnl packet_number_length) packet_number
  | BLong version dcid dcil scid scil spec ->
    MLong version (FB.hide (B.as_seq m dcid)) (FB.hide (B.as_seq m scid))
      begin match spec with
      | BInitial payload_and_pn_length packet_number_length token token_length ->
        MInitial (FB.hide (B.as_seq m token)) (u62_of_su62 (SecretIntegers.to_u64 payload_and_pn_length `SecretIntegers.sub` SecretIntegers.to_u64 packet_number_length)) (pnl_of_spnl packet_number_length) packet_number
      | BZeroRTT payload_and_pn_length packet_number_length ->
        MZeroRTT (u62_of_su62 (SecretIntegers.to_u64 payload_and_pn_length `SecretIntegers.sub` SecretIntegers.to_u64 packet_number_length)) (pnl_of_spnl packet_number_length) packet_number
      | BHandshake payload_and_pn_length packet_number_length ->
        MHandshake (u62_of_su62 (SecretIntegers.to_u64 payload_and_pn_length `SecretIntegers.sub` SecretIntegers.to_u64 packet_number_length)) (pnl_of_spnl packet_number_length) packet_number
      | BRetry unused odcid odcil ->
        MRetry unused (FB.hide (B.as_seq m odcid))
      end

#pop-options

let frame_header_live
  (h: header)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (
    header_live h m1 /\
    B.modifies l m1 m2 /\
    B.loc_disjoint l (header_footprint h)
  ))
  (ensures (header_live h m2))
= ()

let frame_header
  (h: header)
  (packet_number: uint62_t)
  (l: B.loc)
  (m1 m2: HS.mem)
: Lemma
  (requires (
    header_live h m1 /\
    B.modifies l m1 m2 /\
    B.loc_disjoint l (header_footprint h)
  ))
  (ensures (header_live h m2 /\ g_header h m2 packet_number == g_header h m1 packet_number))
= ()

(* Length computations need to be transparent because the precondition
to QUIC.Impl.encrypt requires the user to provide a destination buffer
large enough to contain the byte representation of the header *)

let varint_len
  (x: U64.t)
: Tot (y: U32.t {U32.v y <= 8})
= if x `U64.lt` 64uL
  then 1ul
  else if x `U64.lt` 16384uL
  then 2ul
  else if x `U64.lt` 1073741824uL
  then 4ul
  else 8ul

// TODO: replace (varint_len payload_length) with (varint_len (payload_length + pn_length) in the code below

module Cast = FStar.Int.Cast

#push-options "--z3rlimit 64"

let header_len
  (h: header)
: Tot SecretIntegers.uint32
= match h with
  | BShort spin phase cid cid_len packet_number_length ->
    SecretIntegers.to_u32 (1ul `U32.add` cid_len) `SecretIntegers.add` packet_number_length
  | BLong version dcid dcil scid scil spec ->
    SecretIntegers.to_u32 (7ul `U32.add` dcil `U32.add` scil) `SecretIntegers.add`
    begin match spec with
    | BInitial payload_and_pn_length packet_number_length token token_length ->
      SecretIntegers.to_u32 (varint_len (Cast.uint32_to_uint64 token_length) `U32.add` token_length `U32.add` varint_len payload_and_pn_length) `SecretIntegers.add` packet_number_length
    | BZeroRTT payload_and_pn_length packet_number_length ->
      SecretIntegers.to_u32 (varint_len payload_and_pn_length) `SecretIntegers.add` packet_number_length
    | BHandshake payload_and_pn_length packet_number_length ->
      SecretIntegers.to_u32 (varint_len payload_and_pn_length) `SecretIntegers.add` packet_number_length
    | BRetry unused odcid odcil ->
      SecretIntegers.to_u32 (1ul `U32.add` odcil)
    end

#pop-options
