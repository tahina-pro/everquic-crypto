module QUIC.Parse.VarInt

module U64 = FStar.UInt64
module LP = LowParse.Spec.Base

inline_for_extraction
let varint_bound : (varint_bound: U64.t { U64.v varint_bound == pow2 62 }) =
  [@inline_let] let v = 4611686018427387904uL in
  [@inline_let] let _ = assert_norm (U64.v v == pow2 62) in
  v

inline_for_extraction
let varint_t = (x: U64.t { U64.v x < U64.v varint_bound })

inline_for_extraction
let parse_varint_kind = {
  LP.parser_kind_low = 1;
  LP.parser_kind_high = Some 8;
  LP.parser_kind_subkind = Some LP.ParserStrong;
  LP.parser_kind_metadata = None;
}

val parse_varint : LP.parser parse_varint_kind varint_t