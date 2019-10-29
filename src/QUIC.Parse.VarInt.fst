module QUIC.Parse.VarInt

open LowParse.Spec.BoundedInt
open LowParse.Spec.BitFields

inline_for_extraction
let parse_varint_payload_kind = {
  parser_kind_low = 0;
  parser_kind_high = Some 7;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

module Cast = FStar.Int.Cast
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8

inline_for_extraction
let varint_msb_t = (x: U64.t { U64.v x < 64 })

#push-options "--z3rlimit 32"

inline_for_extraction
let synth_u14
  (msb: varint_msb_t)
  (lsb: U8.t)
: Tot varint_t
= [@inline_let] let _ =
    assert_norm (pow2 8 == 256);
    assert (pow2 62 == U64.v varint_bound)
  in
  (msb `U64.mul` 256uL) `U64.add` Cast.uint8_to_uint64 lsb  

let synth_u14_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u14 msb))
  [SMTPat (synth_injective (synth_u14 msb))]
= ()

inline_for_extraction
let synth_u30
  (msb: varint_msb_t)
  (lsb: bounded_integer 3)
: Tot varint_t
= [@inline_let] let _ =
    assert_norm (pow2 8 == 256);
    assert (pow2 62 == U64.v varint_bound);
    assert_norm (pow2 24 == 16777216)
   in
   (msb `U64.mul` 16777216uL) `U64.add` Cast.uint32_to_uint64 lsb

let synth_u30_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u30 msb))
  [SMTPat (synth_injective (synth_u30 msb))]
= ()

inline_for_extraction
let synth_u62
  (msb: varint_msb_t)
  (lsb: (U32.t & bounded_integer 3))
: Tot varint_t
= [@inline_let] let _ =
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296)
  in
  match lsb with
  | (hi, lo) ->
  Cast.uint32_to_uint64 lo `U64.add` (16777216uL `U64.mul` (Cast.uint32_to_uint64 hi `U64.add` (4294967296uL `U64.mul` msb)))

let synth_u62_msb
  (msb: varint_msb_t)
  (lsb: (U32.t & bounded_integer 3))
: Lemma
  (U64.v (synth_u62 msb lsb) / 72057594037927936 == U64.v msb)
= ()

let synth_u62_injective
  (msb: varint_msb_t)
: Lemma
  (synth_injective (synth_u62 msb))
  [SMTPat (synth_injective (synth_u62 msb))]
= ()

inline_for_extraction
let filter_u14
  (y: varint_t)
: Tot bool
= 64uL `U64.lte` y

inline_for_extraction
let filter_u30
  (y: varint_t)
: Tot bool
= 16384uL `U64.lte` y

inline_for_extraction
let filter_u62
  (y: varint_t)
: Tot bool
= 1073741824uL `U64.lte` y
    
inline_for_extraction
let id_u14
  (y: parse_filter_refine filter_u14)
: Tot varint_t
= y

let parse_varint_payload_u14
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    (((parse_u8 `parse_synth` synth_u14 msb)
    `parse_filter` filter_u14)
    `parse_synth` id_u14)
    
inline_for_extraction
let id_u30
  (y: parse_filter_refine filter_u30)
: Tot varint_t
= y

let parse_varint_payload_u30
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    (((parse_bounded_integer 3 `parse_synth` synth_u30 msb)
    `parse_filter` filter_u30)
    `parse_synth` id_u30)

inline_for_extraction
let id_u62
  (y: parse_filter_refine filter_u62)
: Tot varint_t
= y

let p7 = parse_u32 `nondep_then` parse_bounded_integer 3

let parse_varint_payload_u62
  (msb: varint_msb_t)
: Tot (parser parse_varint_payload_kind varint_t)
= 
  weaken parse_varint_payload_kind
    ((((p7) `parse_synth` synth_u62 msb)
    `parse_filter` filter_u62)
    `parse_synth` id_u62)

let parse_varint_payload_14_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u14 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u14 msb) b in
    64 <= U64.v v /\
    U64.v v < 16384 /\
    U64.v msb == U64.v v / 256
  ))
= 
   assert_norm (pow2 6 == 64);
   assert_norm (pow2 8 == 256);
   assert (pow2 62 == U64.v varint_bound);
   assert_norm (pow2 32 == 4294967296);
   assert_norm (pow2 24 == 16777216);
   parse_synth_eq parse_u8 (synth_u14 msb) b;
   parse_filter_eq (parse_u8 `parse_synth` (synth_u14 msb)) filter_u14 b;
   parse_synth_eq ((parse_u8 `parse_synth` (synth_u14 msb)) `parse_filter` filter_u14) id_u14 b

let parse_varint_payload_30_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u30 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u30 msb) b in
    16384 <= U64.v v /\
    U64.v v < 1073741824 /\
    U64.v msb == U64.v v / 16777216
  ))
= 
    parse_synth_eq (parse_bounded_integer 3) (synth_u30 msb) b;
    parse_filter_eq (parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) filter_u30 b;
    parse_synth_eq ((parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) `parse_filter` filter_u30) (id_u30) b

let parse_varint_payload_62_interval
  (msb: varint_msb_t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload_u62 msb) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload_u62 msb) b in
    1073741824 <= U64.v v /\
    U64.v msb == U64.v v / (72057594037927936)
  ))
= 
   assert_norm (pow2 6 == 64);
   assert_norm (pow2 8 == 256);
   assert (pow2 62 == U64.v varint_bound);
   assert_norm (pow2 32 == 4294967296);
   assert_norm (pow2 24 == 16777216);
   parse_synth_eq (p7) (synth_u62 msb) b;
   parse_filter_eq ((p7) `parse_synth` synth_u62 msb) filter_u62 b;
   parse_synth_eq (((p7) `parse_synth` (synth_u62 msb)) `parse_filter` filter_u62) (id_u62) b;
   let Some (v, _) = parse (parse_varint_payload_u62 msb) b in
   let Some (lsb, _) = parse (p7) b in
   synth_u62_msb msb lsb

let parse_varint_payload
  (x: U8.t)
: Tot (parser parse_varint_payload_kind varint_t)
= assert_norm (pow2 6 == 64);
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  let kd = uint8.get_bitfield x 6 8 in
  let msb : varint_msb_t = Cast.uint8_to_uint64 (uint8.get_bitfield x 0 6) in
  if kd = 0uy
  then weaken parse_varint_payload_kind (parse_ret msb)
  else if kd = 1uy
  then parse_varint_payload_u14 msb
  else if kd = 2uy
  then parse_varint_payload_u30 msb
  else parse_varint_payload_u62 msb

module BF = LowParse.BitFields

let parse_varint_payload_interval
  (tag: U8.t)
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_varint_payload tag) b)))
  (ensures (
    let Some (v, _) = parse (parse_varint_payload tag) b in
    let kd = uint8.get_bitfield tag 6 8 in
    let msb = uint8.get_bitfield tag 0 6 in
    (kd == 0uy \/ kd == 1uy \/ kd == 2uy \/ kd == 3uy) /\ (
    if kd = 0uy
    then U64.v v < 64 /\ U8.v msb = U64.v v
    else if kd = 1uy
    then 64 <= U64.v v /\ U64.v v < 16384 /\ U8.v msb == U64.v v / 256
    else if kd = 2uy
    then 16384 <= U64.v v /\ U64.v v < 1073741824 /\ U8.v msb == U64.v v / 16777216
    else 1073741824 <= U64.v v /\ U8.v msb == U64.v v / 72057594037927936
  )))
=
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  let Some (v, _) = parse (parse_varint_payload tag) b in
  let kd = uint8.get_bitfield tag 6 8 in
  assert (kd == 0uy \/ kd == 1uy \/ kd == 2uy \/ kd == 3uy);
  let msb8 = uint8.get_bitfield tag 0 6 in
  let msb = Cast.uint8_to_uint64 msb8 in
  if kd = 0uy
  then begin
    assert (U64.v v < 64);
    assert (U8.v msb8 == U64.v v)
  end
  else if kd = 1uy
  then begin
    parse_varint_payload_14_interval msb b
  end else if kd = 2uy
  then
    parse_varint_payload_30_interval msb b
  else
    parse_varint_payload_62_interval msb b

#pop-options

let parse_varint_payload_and_then_cases_injective : squash (and_then_cases_injective parse_varint_payload) =
  assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 24 == 16777216);
  and_then_cases_injective_intro parse_varint_payload (fun x1 x2 b1 b2 ->
    let msb1 = Cast.uint8_to_uint64 (uint8.get_bitfield x1 0 6) in
    let msb2 = Cast.uint8_to_uint64 (uint8.get_bitfield x2 0 6) in
    parse_varint_payload_interval x1 b1;
    parse_varint_payload_interval x2 b2;
    assert (uint8.v (uint8.get_bitfield x1 6 8) == uint8.v (uint8.get_bitfield x2 6 8));
    assert (uint8.v (uint8.get_bitfield x1 0 6) == uint8.v (uint8.get_bitfield x2 0 6));
    BF.get_bitfield_partition_2 6 (U8.v x1) (U8.v x2)
  )

let parse_varint =
  parse_u8 `and_then` parse_varint_payload

let parse_varint_eq_aux
  (b: bytes)
: Lemma
  (pow2 8 == 256 /\ pow2 62 == U64.v varint_bound /\ pow2 24 == 16777216 /\ pow2 32 == 4294967296 /\
  parse parse_varint b == (match parse parse_u8 b with
  | None -> None
  | Some (hd, consumed) ->
    let b' = Seq.slice b consumed (Seq.length b) in
    match parse (parse_varint_payload hd) b' with
    | None -> None
    | Some (res, consumed') -> Some (res, consumed + consumed')
  ))
= assert_norm (pow2 8 == 256);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  and_then_eq parse_u8 parse_varint_payload b

#push-options "--z3rlimit 128"

let parse_varint'
  (b: bytes)
: GTot (option (varint_t & consumed_length b))
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  match parse parse_u8 b with
  | None -> None
  | Some (hd, consumed) ->
    let tag = uint8.get_bitfield hd 6 8 in
    let msb = Cast.uint8_to_uint64 (uint8.get_bitfield hd 0 6) in
    let b' = Seq.slice b consumed (Seq.length b) in
    if tag = 0uy
    then
      Some ((msb <: varint_t), consumed)
    else if tag = 1uy
    then begin match parse parse_u8 b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : varint_t = (msb `U64.mul` 256uL) `U64.add` Cast.uint8_to_uint64 lsb in
      if 64uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
      end
    else if tag = 2uy
    then begin match parse (parse_bounded_integer 3) b' with
    | None -> None
    | Some (lsb, consumed') ->
      let v : varint_t =
        (msb `U64.mul` 16777216uL) `U64.add` Cast.uint32_to_uint64 lsb
      in
      if 16384uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
    end else begin match parse (parse_u32 `nondep_then` parse_bounded_integer 3) b' with
    | None -> None
    | Some ((hi, lo), consumed') ->
      let v : varint_t =
        Cast.uint32_to_uint64 lo `U64.add` (16777216uL `U64.mul` (Cast.uint32_to_uint64 hi `U64.add` (4294967296uL `U64.mul` msb)))
      in
      if 1073741824uL `U64.lte` v
      then Some (v, consumed + consumed')
      else None
    end

let parse_varint_eq
  (b: bytes)
: Lemma
  (pow2 8 == 256 /\ pow2 62 == U64.v varint_bound /\ pow2 24 == 16777216 /\ pow2 32 == 4294967296 /\
  parse parse_varint b == parse_varint' b)
= assert_norm (pow2 8 == 256);
  assert_norm (pow2 6 == 64);
  assert (pow2 62 == U64.v varint_bound);
  assert_norm (pow2 24 == 16777216);
  assert_norm (pow2 32 == 4294967296);
  parse_varint_eq_aux b;
  match parse parse_u8 b with
  | None -> ()
  | Some (hd, consumed) ->
    let tag = uint8.get_bitfield hd 6 8 in
    let msb8 = uint8.get_bitfield hd 0 6 in
    let msb = Cast.uint8_to_uint64 msb8 in
    let b' = Seq.slice b consumed (Seq.length b) in
    assert (tag == 0uy \/ tag == 1uy \/ tag == 2uy \/ tag == 3uy);
    if tag = 0uy
    then ()
    else if tag = 1uy
    then begin
      parse_synth_eq parse_u8 (synth_u14 msb) b';
      parse_filter_eq (parse_u8 `parse_synth` (synth_u14 msb)) filter_u14 b';
      parse_synth_eq ((parse_u8 `parse_synth` (synth_u14 msb)) `parse_filter` filter_u14) id_u14 b'
    end else if tag = 2uy
    then begin
      parse_synth_eq (parse_bounded_integer 3) (synth_u30 msb) b';
      parse_filter_eq (parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) filter_u30 b';
      parse_synth_eq ((parse_bounded_integer 3 `parse_synth` (synth_u30 msb)) `parse_filter` filter_u30) id_u30 b'
    end else begin
      parse_synth_eq (p7) (synth_u62 msb) b';
      parse_filter_eq (p7 `parse_synth` (synth_u62 msb)) filter_u62 b';
      parse_synth_eq ((p7 `parse_synth` (synth_u62 msb)) `parse_filter` filter_u62) id_u62 b'
    end

#pop-options
