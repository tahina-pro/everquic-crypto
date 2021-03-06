/// An implementation of QUIC.Spec.fst that is concerned only with functional
/// correctness (no notion of model for now).
module QUIC.Impl

// This MUST be kept in sync with QUIC.Impl.fst...
module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST


module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

#set-options "--max_fuel 0 --max_ifuel 0"
// ... up to here!

unfold noextract
let hash_alg = Spec.Hash.Definitions.hash_alg

unfold noextract
let aead_alg = Spec.Agile.AEAD.alg

unfold noextract
let lbytes = QUIC.Spec.lbytes

/// This is not a cryptographic index; rather, this is just a regular type
/// index, where instead of indexing on a single algorithm (like, say, AEAD), we
/// index on two values.
///
/// The record is here to limit the profileration of hide/reveal in the stateful
/// functions, and to give easier projectors (ADL, JP).
type index = {
  hash_alg: QUIC.Spec.ha;
  aead_alg: QUIC.Spec.ea
}

/// Low-level types used in this API
/// --------------------------------

type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}

/// Boilerplate
/// -----------

[@CAbstractStruct]
val state_s: index -> Type0

let state i = B.pointer (state_s i)

val footprint_s: #i:index -> HS.mem -> state_s i -> GTot B.loc
let footprint (#i:index) (m: HS.mem) (s: state i) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s m (B.deref m s)))

let loc_includes_union_l_footprint_s
  (m: HS.mem)
  (l1 l2: B.loc) (#a: index) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s m s) \/ B.loc_includes l2 (footprint_s m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s m s))]
= B.loc_includes_union_l l1 l2 (footprint_s m s)

/// Ghost accessors (not needing the invariant)
/// -------------------------------------------
///
/// We need to define those, so that we can state a framing lemma for them.
/// Attempting a new convention to distinguish ghost accessors from stateful
/// functions: a ``g_`` prefix.

/// See remark for ``g_initial_packet_number`` below.
val g_traffic_secret: #i:index -> (s: state_s i) ->
  GTot (Spec.Hash.Definitions.bytes_hash i.hash_alg)

#push-options "--max_ifuel 1" // inversion on hash_alg
let hash_is_keysized #i (s: state_s i): Lemma
  (ensures (QUIC.Spec.keysized i.hash_alg (S.length (g_traffic_secret s))))
  [ SMTPat (g_traffic_secret s) ]
=
  assert_norm (512 < pow2 61);
  assert_norm (512 < pow2 125)
#pop-options

/// Note that this one does *NOT* take the memory as an argument. (This is
/// because the initial packet number is erased in the concrete state.) Callers
/// should be able to derive, from this, that the initial packet number remains
/// the same, thanks to the precise use of footprint_s in encrypt/decrypt.
val g_initial_packet_number: #i:index -> (s: state_s i) -> GTot QUIC.Spec.nat62

/// Invariant
/// ---------

val invariant_s: (#i:index) -> HS.mem -> state_s i -> Type0
let invariant (#i:index) (m: HS.mem) (s: state i) =
  let r = B.frameOf s in
  ST.is_eternal_region r /\
  B.loc_includes (B.loc_region_only true r) (footprint m s) /\
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s m (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#i: index)
  (s: state i)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]


/// Ghost accessors needing the invariant
/// -------------------------------------

val g_packet_number: #i:index -> (s: state_s i) -> (h: HS.mem { invariant_s h s }) ->
  GTot (pn:QUIC.Spec.nat62{
    pn >= g_initial_packet_number s
  })

let incrementable (#i: index) (s: state i) (h: HS.mem { invariant h s }) =
  g_packet_number (B.deref h s) h + 1 < pow2 62

/// Preserving all the ghost accessors via a single framing lemma only works
/// because we don't do stack allocation. See comments in
/// EverCrypt.Hash.Incremental.
val frame_invariant: #i:index -> l:B.loc -> s:state i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s /\
    g_packet_number (B.deref h0 s) h0 == g_packet_number (B.deref h1 s) h0 /\
    g_traffic_secret (B.deref h0 s) == g_traffic_secret (B.deref h1 s)
    ))
  // Assertion failure: unexpected pattern term
  (*[ SMTPat (B.modifies l h0 h1); SMTPatOr [
    [ SMTPat (invariant h1 s) ];
    [ SMTPat (footprint h1 s) ];
    [ SMTPat (g_aead_key (B.deref h1 s)) ];
    [ SMTPat (g_counter (B.deref h1 s)) ]
  ]]*)


let add3 (k:u4):
  n:U8.t { U8.v n <= 18 /\ U8.v n = QUIC.Spec.add3 (U8.v k) }
=
  if k = 0uy then 0uy else U8.(k +^ 3uy)

/// Information stored in a QUIC header. This is a Low* type passed by value --
/// it's a little expensive. Consider passing it by reference in ``encrypt``?
///
/// Note that we try to follow the convention of buffer arguments followed by
/// their lengths.
noeq type header =
  | Short:
    spin: bool ->
    phase: bool ->
    cid: B.buffer U8.t ->
    cid_len: U8.t{
      let l = U8.v cid_len in
      (l == 0 \/ (4 <= l /\ l <= 18)) /\
      U8.v cid_len == B.length cid
    } ->
    header

  | Long:
    typ: u2 ->
    version: U32.t ->
    dcid: B.buffer U8.t ->
    dcil: u4 { B.length dcid == U8.v (add3 dcil) } ->
    scid: B.buffer U8.t ->
    scil: u4 { B.length scid == U8.v (add3 scil) } ->
    plain_len: U32.t{U32.v plain_len < QUIC.Spec.max_cipher_length} ->
    header

let _: squash (inversion header) = allow_inversion header

let header_live (h: header) (m: HS.mem) =
  match h with
  | Short _ _ cid _ -> m `B.live` cid
  | Long _ _ dcid _ scid _ _ -> m `B.live` dcid /\ m `B.live` scid

let header_footprint (h: header) =
  let open B in
  match h with
  | Short _ _ cid _ -> loc_buffer cid
  | Long _ _ dcid _ scid _ _ -> loc_buffer dcid `loc_union` loc_buffer scid

let header_disjoint (h: header) =
  let open B in
  match h with
  | Short _ _ cid _ -> True
  | Long _ _ dcid _ scid _ _ -> B.disjoint dcid scid

let g_header (h: header) (m: HS.mem): GTot QUIC.Spec.header =
  match h with
  | Short spin phase cid cid_len ->
      QUIC.Spec.Short spin phase (B.as_seq m cid)
  | Long typ version dcid dcil scid scil plain_len ->
      QUIC.Spec.Long (U8.v typ) (U32.v version) (U8.v dcil) (U8.v scil)
      (B.as_seq m dcid) (B.as_seq m scid) (U32.v plain_len)


/// Actual stateful API
/// -------------------

val aead_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack aead_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).aead_alg /\
    h0 == h1))

val hash_alg_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack hash_alg
  (requires (fun h0 -> invariant #(G.reveal i) h0 s))
  (ensures (fun h0 a h1 ->
    a == (G.reveal i).hash_alg /\
    h0 == h1))

val packet_number_of_state (#i: G.erased index) (s: state (G.reveal i)): Stack U64.t
  (requires fun h0 -> invariant h0 s)
  (ensures fun h0 ctr h1 ->
    U64.v ctr == g_packet_number (B.deref h0 s) h0 /\
    h0 == h1)

// JP: we could be defensive and allow callers to pass potentially unsupported
// algorithms; however, this would require a lot more machinery as we would not
// even be able to state the index type, since index currently has a refinement
// that the two algorithms are supported. We would have to separate index into
// index0 and a well-formedness refinement. Not sure it's worth it. We can
// always perform redundant tests inside the definition of create to be fully
// defensive.
inline_for_extraction noextract
let create_in_st (i:index) =
  r:HS.rid ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  initial_pn:u62 ->
  traffic_secret:B.buffer U8.t {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  ST error_code
    (requires fun h0 ->
      // JP: we could require that ``dst`` point to NULL prior to calling
      // ``create`` (otherwise, it's a memory leak). Other modules don't enforce
      // this (see AEAD) so for now, let's make the caller's life easier and not
      // demand anything.
      ST.is_eternal_region r /\
      B.live h0 dst /\ B.live h0 traffic_secret /\
      B.disjoint dst traffic_secret)
    (ensures (fun h0 e h1 ->
      match e with
      | UnsupportedAlgorithm ->
          B.(modifies loc_none h0 h1)
      | Success ->
          let s = B.deref h1 dst in
          not (B.g_is_null s) /\
          invariant h1 s /\

          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1 /\

          g_initial_packet_number (B.deref h1 s) == U64.v initial_pn
      | _ ->
          False))

// The index is passed at run-time.
val create_in: i:index -> create_in_st i

val encrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s: state i ->
  dst: B.buffer U8.t ->
  h: header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t {
    3 <= U32.v plain_len /\
    U32.v plain_len < QUIC.Spec.max_plain_length /\
    B.length plain = U32.v plain_len
  } ->
  pn_len: u2 ->
  Stack error_code
    (requires fun h0 ->
      // Memory & preservation
      B.live h0 plain /\ B.live h0 dst /\
      header_live h h0 /\
      header_disjoint h /\
      B.(all_disjoint [ footprint h0 s; loc_buffer dst; header_footprint h; loc_buffer plain ]) /\

      invariant h0 s /\

      incrementable s h0 /\ (
      let clen = U32.v plain_len + Spec.Agile.AEAD.tag_length i.aead_alg in
      let len = clen + QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) in
      (Long? h ==> U32.v (Long?.plain_len h) = clen) /\
      B.length dst == len
    ))
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          // Memory & preservation
          B.(modifies (footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst)) h0 h1 /\
          invariant h1 s /\
          footprint_s h1 (B.deref h1 s) == footprint_s h0 (B.deref h0 s) /\ (

          // Functional correctness
          let s0 = g_traffic_secret (B.deref h0 s) in
          let open QUIC.Spec in
          let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
          let iv = derive_secret i.hash_alg s0 label_iv 12 in
          let pne = derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg) in
          let plain: pbytes = B.as_seq h0 plain in
          let packet: packet = B.as_seq h1 dst in
          let ctr = g_packet_number (B.deref h0 s) h0 in
          packet ==
            QUIC.Spec.encrypt i.aead_alg k iv pne (U8.v pn_len) ctr (g_header h h0) plain /\
          g_packet_number (B.deref h1 s) h1 = ctr + 1)
      | _ ->
          False))

val initial_secrets (dst_client: B.buffer U8.t)
  (dst_server: B.buffer U8.t)
  (cid: B.buffer U8.t)
  (cid_len: U32.t):
  Stack unit
    (requires (fun h0 ->
      B.(all_live h0 [ buf dst_client; buf dst_server; buf cid ]) /\
      B.length dst_client = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length dst_server = Spec.Agile.Hash.(hash_length SHA2_256) /\
      B.length cid = U32.v cid_len /\
      U32.v cid_len <= 20 /\
      B.(all_disjoint [ loc_buffer dst_client; loc_buffer dst_server; loc_buffer cid ])))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst_client `loc_union` loc_buffer dst_server) h0 h1)))

// Callers allocate this type prior to calling decrypt. The contents are only
// meaningful, and plain is only non-null, if the decryption was a success.
noeq
type result = {
  pn_len: u2;
  pn: u62;
  header: header;
  header_len: U32.t;
  plain_len: n:U32.t{let l = U32.v n in 3 <= l /\ l < QUIC.Spec.max_plain_length};
  total_len: n:U32.t
}

noextract
let max (x y: nat) = if x >= y then x else y

val decrypt: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst: B.pointer result ->
  packet: B.buffer U8.t ->
  len: U32.t{
    21 <= U32.v len /\ U32.v len < pow2 32 /\
    B.length packet == U32.v len
  } ->
  cid_len: u4 ->
  Stack error_code
    (requires fun h0 ->
      // We require clients to allocate space for a result, e.g.
      //   result r = { 0 };
      //   decrypt(s, &r, ...);
      // This means that we don't require that the pointers inside ``r`` be live
      // (i.e. NO ``header_live header`` precondition).
      // After a successful call to decrypt, ``packet`` contains the decrypted
      // data; ``header`` is modified to point within the header area of
      // ``packet``; and the plaintext is within ``packet`` in range
      // ``[header_len, header_len + plain_len)``.
      B.live h0 packet /\ B.live h0 dst /\
      B.disjoint dst packet /\

      invariant h0 s /\

      incrementable s h0)
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          B.(modifies (footprint_s h0 (deref h0 s) `loc_union`
            loc_buffer packet `loc_union` loc_buffer dst) h0 h1) /\

          invariant h1 s /\
          footprint h1 s == footprint h0 s /\ (

          let r = B.deref h1 dst in
          // prev is known to be >= g_initial_packet_number (see lemma invariant_packet_number)
          let prev = g_packet_number (B.deref h0 s) h0 in
          let curr = g_packet_number (B.deref h1 s) h1 in
          curr == max prev (U64.v r.pn) /\ (

          // Lengths
          let r = B.deref h1 dst in
          U32.v r.total_len = U32.v r.header_len + U32.v r.plain_len +
            Spec.Agile.AEAD.tag_length i.aead_alg /\
          U32.v r.header_len = QUIC.Spec.header_len (g_header r.header h1) (U8.v r.pn_len) /\ (

          let s0 = g_traffic_secret (B.deref h0 s) in
          let k = QUIC.Spec.(derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg)) in
          let iv = QUIC.Spec.(derive_secret i.hash_alg s0 label_iv 12) in
          let pne = QUIC.Spec.(derive_secret i.hash_alg s0 label_hp (ae_keysize i.aead_alg)) in
          U32.v r.total_len <= B.length packet /\ (
          let plain: QUIC.Spec.pbytes =
            S.slice (B.as_seq h1 packet) (U32.v r.header_len)
              (U32.v r.header_len + U32.v r.plain_len) in
          let packet: QUIC.Spec.packet = S.slice (B.as_seq h0 packet) 0 (U32.v r.total_len) in
          (Long? r.header ==> cid_len = 0uy) /\
          QUIC.Spec.decrypt i.aead_alg k iv pne prev (U8.v cid_len) packet
            == QUIC.Spec.Success (U8.v r.pn_len) (U64.v r.pn) (g_header r.header h1) plain))))
      | _ ->
          False))
