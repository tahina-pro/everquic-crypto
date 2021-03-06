module QUIC.Impl

// This MUST be kept in sync with QUIC.Impl.fsti...
module G = FStar.Ghost
module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
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

module Cipher = EverCrypt.Cipher
module AEAD = EverCrypt.AEAD
module HKDF = EverCrypt.HKDF
module CTR = EverCrypt.CTR

friend QUIC.Spec

open LowStar.BufferOps

inline_for_extraction noextract
let as_cipher_alg (a: QUIC.Spec.ea): a:Spec.Agile.Cipher.cipher_alg {
  Spec.Agile.Cipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20)
} =
  Spec.Agile.AEAD.cipher_alg_of_supported_alg a

/// https://tools.ietf.org/html/draft-ietf-quic-tls-23#section-5
///
/// We perform the three key derivations (AEAD key; AEAD iv; header protection
/// key) when ``create`` is called. We thus store the original traffic secret
/// only ghostly.
///
/// We retain the AEAD state, in order to perform the packet payload encryption.
///
/// We retain the Cipher state, in order to compute the mask for header protection.
noeq
type state_s (i: index) =
  | State:
      the_hash_alg:hash_alg { the_hash_alg == i.hash_alg } ->
      the_aead_alg:aead_alg { the_aead_alg == i.aead_alg } ->
      traffic_secret:G.erased (Spec.Hash.Definitions.bytes_hash the_hash_alg) ->
      initial_pn:G.erased QUIC.Spec.nat62 ->
      aead_state:EverCrypt.AEAD.state the_aead_alg ->
      iv:EverCrypt.AEAD.iv_p the_aead_alg ->
      hp_key:B.buffer U8.t { B.length hp_key = QUIC.Spec.ae_keysize the_aead_alg } ->
      pn:B.pointer u62 ->
      ctr_state:CTR.state (as_cipher_alg the_aead_alg) ->
      state_s i

let footprint_s #i h s =
  let open LowStar.Buffer in
  AEAD.footprint h (State?.aead_state s) `loc_union`
  CTR.footprint h (State?.ctr_state s) `loc_union`
  loc_buffer (State?.iv s) `loc_union`
  loc_buffer (State?.hp_key s) `loc_union`
  loc_buffer (State?.pn s)

let g_traffic_secret #i s =
  // Automatic reveal insertion doesn't work here
  G.reveal (State?.traffic_secret s)

let g_initial_packet_number #i s =
  // New style: automatic insertion of reveal
  State?.initial_pn s

let invariant_s #i h s =
  let open QUIC.Spec in
  let State hash_alg aead_alg traffic_secret initial_pn aead_state iv hp_key pn ctr_state =
    s in
  hash_is_keysized s; (
  AEAD.invariant h aead_state /\
  not (B.g_is_null aead_state) /\
  CTR.invariant h ctr_state /\
  not (B.g_is_null ctr_state) /\
  B.(all_live h [ buf iv; buf hp_key; buf pn ])  /\
  B.(all_disjoint [ CTR.footprint h ctr_state;
    AEAD.footprint h aead_state; loc_buffer iv; loc_buffer hp_key; loc_buffer pn ]) /\
  // JP: automatic insertion of reveal does not work here
  G.reveal initial_pn <= U64.v (B.deref h pn) /\
  AEAD.as_kv (B.deref h aead_state) ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_key (Spec.Agile.AEAD.key_length aead_alg) /\
  B.as_seq h iv ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_iv 12 /\
  B.as_seq h hp_key ==
    derive_secret i.hash_alg (G.reveal traffic_secret) label_hp (QUIC.Spec.ae_keysize aead_alg)
  )

let invariant_loc_in_footprint #_ _ _ = ()

let g_packet_number #i s h =
  U64.v (B.deref h (State?.pn s))

let frame_invariant #i l s h0 h1 =
  AEAD.frame_invariant l (State?.aead_state (B.deref h0 s)) h0 h1;
  CTR.frame_invariant l (State?.ctr_state (B.deref h0 s)) h0 h1

let aead_alg_of_state #i s =
  let State _ the_aead_alg _ _ _ _ _ _ _ = !*s in
  the_aead_alg

let hash_alg_of_state #i s =
  let State the_hash_alg _ _ _ _ _ _ _ _ = !*s in
  the_hash_alg

let packet_number_of_state #i s =
  let State _ _ _ _ _ _ _ pn _ = !*s in
  !*pn

/// Helpers & globals
/// -----------------

friend QUIC.Impl.Lemmas
open QUIC.Impl.Lemmas

inline_for_extraction noextract
let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32
inline_for_extraction noextract
let u64_of_u8 = FStar.Int.Cast.uint8_to_uint64
inline_for_extraction noextract
let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64

let key_len (a: QUIC.Spec.ea): x:U8.t { U8.v x = Spec.Agile.AEAD.key_length a } =
  let open Spec.Agile.AEAD in
  match a with
  | AES128_GCM -> 16uy
  | AES256_GCM -> 32uy
  | CHACHA20_POLY1305 -> 32uy

let key_len32 a = FStar.Int.Cast.uint8_to_uint32 (key_len a)

#push-options "--warn_error -272"
let label_key = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_key_l
let label_iv = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_iv_l
let label_hp = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.label_hp_l
let prefix = LowStar.ImmutableBuffer.igcmalloc_of_list HS.root QUIC.Spec.prefix_l
#pop-options

/// Actual code
/// -----------

#push-options "--z3rlimit 200"
inline_for_extraction noextract
let op_inplace (dst: B.buffer U8.t)
  (dst_len: U32.t)
  (src: B.buffer U8.t)
  (src_len: U32.t)
  (ofs: U32.t)
  (op: U8.t -> U8.t -> U8.t)
:
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf src ]) /\
      B.disjoint dst src /\
      B.length src = U32.v src_len /\
      B.length dst = U32.v dst_len /\
      B.length dst >= U32.v ofs + B.length src)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        QUIC.Spec.pointwise_op op (B.as_seq h0 dst) (B.as_seq h0 src) (U32.v ofs) /\
      S.slice (B.as_seq h0 dst) 0 (U32.v ofs) `S.equal`
        S.slice (B.as_seq h1 dst) 0 (U32.v ofs) /\
      S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len) `S.equal`
      S.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (U32.v dst_len))
=
  let h0 = ST.get () in
  let dst0 = B.sub dst 0ul ofs in
  let dst1 = B.sub dst ofs src_len in
  let dst2 = B.sub dst (ofs `U32.add` src_len) (dst_len `U32.sub` (ofs `U32.add` src_len)) in
  C.Loops.in_place_map2 dst1 src src_len op;
  let h1 = ST.get () in
  calc (S.equal) {
    B.as_seq h1 dst;
  (S.equal) { lemma_slice3 (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    S.slice (B.as_seq h1 dst) 0 (U32.v ofs) `S.append`
    (S.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `S.append`
    (S.slice (B.as_seq h1 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (S.equal) {}
    S.slice (B.as_seq h0 dst) 0 (U32.v ofs) `S.append`
    (S.slice (B.as_seq h1 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))) `S.append`
    (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (S.equal) { pointwise_seq_map2 op (B.as_seq h0 dst1) (B.as_seq h0 src) 0 }
    S.slice (B.as_seq h0 dst) 0 (U32.v ofs) `S.append`
    (QUIC.Spec.pointwise_op op
      (S.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      0) `S.append`
    (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (S.equal) { QUIC.Spec.pointwise_op_suff op (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
    (S.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)))
    (B.as_seq h0 src)
    (U32.v ofs) }
    QUIC.Spec.pointwise_op op
      (S.append (S.slice (B.as_seq h0 dst) 0 (U32.v ofs))
        (S.slice (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len))))
      (B.as_seq h0 src)
      (U32.v ofs) `S.append`
    (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (S.equal) { lemma_slice1 (B.as_seq h0 dst) (U32.v ofs) (U32.v (ofs `U32.add` src_len)) }
    QUIC.Spec.pointwise_op op
      (S.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
      (B.as_seq h0 src)
      (U32.v ofs) `S.append`
    (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst));
  (S.equal) { QUIC.Spec.pointwise_op_pref op
    (S.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)))
    (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst))
    (B.as_seq h0 src)
    (U32.v ofs)
  }
    QUIC.Spec.pointwise_op op
      (S.slice (B.as_seq h0 dst) 0 (U32.v (ofs `U32.add` src_len)) `S.append`
      (S.slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) (B.length dst)))
      (B.as_seq h0 src)
      (U32.v ofs);
  (S.equal) { lemma_slice (B.as_seq h0 dst) (U32.v (ofs `U32.add` src_len)) }
    QUIC.Spec.pointwise_op op
      (B.as_seq h0 dst)
      (B.as_seq h0 src)
      (U32.v ofs);
  }

#push-options "--max_ifuel 1 --initial_ifuel 1"
/// One ifuel for inverting on the hash algorithm for computing bounds (the
/// various calls to assert_norm should help ensure this proof goes through
/// reliably). Note that I'm breaking from the usual convention where lengths
/// are UInt32's, mostly to avoid trouble reasoning with modulo when casting
/// from UInt32 to UInt8 to write the label for the key derivation. This could
/// be fixed later.
val derive_secret: a: QUIC.Spec.ha ->
  dst:B.buffer U8.t ->
  dst_len: U8.t { B.length dst = U8.v dst_len /\ U8.v dst_len <= 255 } ->
  secret:B.buffer U8.t { B.length secret = Spec.Hash.Definitions.hash_length a } ->
  label:IB.ibuffer U8.t ->
  label_len:U8.t { IB.length label = U8.v label_len /\ U8.v label_len <= 244 } ->
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf secret; buf label; buf dst ]) /\
      B.disjoint dst secret)
    (ensures fun h0 _ h1 ->
      assert_norm (255 < pow2 61);
      assert_norm (pow2 61 < pow2 125);
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == QUIC.Spec.derive_secret a (B.as_seq h0 secret)
        (IB.as_seq h0 label) (U8.v dst_len))
#pop-options

#push-options "--z3rlimit 100"
let derive_secret a dst dst_len secret label label_len =
  LowStar.ImmutableBuffer.recall prefix;
  LowStar.ImmutableBuffer.recall_contents prefix QUIC.Spec.prefix;
  (**) let h0 = ST.get () in

  push_frame ();
  (**) let h1 = ST.get () in

  let label_len32 = FStar.Int.Cast.uint8_to_uint32 label_len in
  let dst_len32 = FStar.Int.Cast.uint8_to_uint32 dst_len in
  let info_len = U32.(1ul +^ 1ul +^ 1ul +^ 11ul +^ label_len32 +^ 1ul) in
  let info = B.alloca 0uy info_len in

  // JP: best way to reason about this sort of code is to slice the buffer very thinly
  let info_z = B.sub info 0ul 1ul in
  let info_lb = B.sub info 1ul 1ul in
  let info_llen = B.sub info 2ul 1ul in
  let info_prefix = B.sub info 3ul 11ul in
  let info_label = B.sub info 14ul label_len32 in
  let info_z' = B.sub info (14ul `U32.add` label_len32) 1ul in
  (**) assert (14ul `U32.add` label_len32 `U32.add` 1ul = B.len info);
  (**) assert B.(all_disjoint [ loc_buffer info_z; loc_buffer info_lb; loc_buffer info_llen;
  (**)   loc_buffer info_prefix; loc_buffer info_label; loc_buffer info_z' ]);

  info_lb.(0ul) <- dst_len;
  info_llen.(0ul) <- U8.(label_len +^ 11uy);
  B.blit prefix 0ul info_prefix 0ul 11ul;
  B.blit label 0ul info_label 0ul label_len32;

  (**) let h2 = ST.get () in
  (**) assert (
  (**)   let z = S.create 1 0uy in
  (**)   let lb = S.create 1 dst_len in // len <= 255
  (**)   let llen = S.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   B.as_seq h2 info_z `Seq.equal` z /\
  (**)   B.as_seq h2 info_lb `Seq.equal` lb /\
  (**)   B.as_seq h2 info_llen `Seq.equal` llen /\
  (**)   B.as_seq h2 info_prefix `Seq.equal` QUIC.Spec.prefix /\
  (**)   B.as_seq h2 info_label `Seq.equal` (B.as_seq h0 label) /\
  (**)   B.as_seq h2 info_z' `Seq.equal` z
  (**) );
  (**) (
  (**)   let z = S.create 1 0uy in
  (**)   let lb = S.create 1 dst_len in // len <= 255
  (**)   let llen = S.create 1 (U8.uint_to_t (11 + Seq.length (B.as_seq h0 label))) in
  (**)   let info = B.as_seq h2 info in
  (**)   lemma_five_cuts info 1 2 3 14 (14 + U8.v label_len)
  (**)     z lb llen QUIC.Spec.prefix (B.as_seq h0 label) z
  (**) );
  (**) hash_is_keysized_ a;
  HKDF.expand a dst secret (Hacl.Hash.Definitions.hash_len a) info info_len dst_len32;
  (**) let h3 = ST.get () in
  pop_frame ();
  (**) let h4 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1 (B.loc_buffer dst) h3 h4;
  (**) assert (ST.equal_domains h0 h4)
#pop-options

/// For functions that perform allocations, or even functions that need
/// temporary state, a style we adopt here is to write the core (i.e. what would
/// normally go in-between push and pop frame) as a separate function. If
/// needed, the core of the function takes its temporary allocations as
/// parameters, and reasons abstractly against a region where the temporary
/// allocations live. This gives significantly better proof performance.
///
/// Another bit of style: after every stateful operation, we restore manually:
/// the modifies clause (going directly for the one we want); the invariant; the
/// footprint preservation; then the functional correctness propertise we are
/// seeking.

val create_in_core:
  i:index ->
  r:HS.rid ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  initial_pn:u62 ->
  traffic_secret:B.buffer U8.t {
    B.length traffic_secret = Spec.Hash.Definitions.hash_length i.hash_alg
  } ->
  aead_state:AEAD.state i.aead_alg ->
  ctr_state:CTR.state (as_cipher_alg i.aead_alg) ->
  ST unit
    (requires fun h0 ->
      QUIC.Impl.Lemmas.hash_is_keysized_ i.hash_alg; (
      ST.is_eternal_region r /\
      B.live h0 dst /\ B.live h0 traffic_secret /\
      B.(all_disjoint [ AEAD.footprint h0 aead_state; CTR.footprint h0 ctr_state;
        loc_buffer dst; loc_buffer traffic_secret ]) /\
      B.(loc_includes (loc_region_only true r) (AEAD.footprint h0 aead_state)) /\
      B.(loc_includes (loc_region_only true r) (CTR.footprint h0 ctr_state)) /\

      // Whatever from the invariant ought to be established already.
      AEAD.invariant h0 aead_state /\
      not (B.g_is_null aead_state) /\
      CTR.invariant h0 ctr_state /\
      not (B.g_is_null ctr_state) /\
      AEAD.as_kv (B.deref h0 aead_state) ==
        QUIC.Spec.(derive_secret i.hash_alg (B.as_seq h0 traffic_secret) label_key
          (Spec.Agile.AEAD.key_length i.aead_alg))))
    (ensures (fun h0 _ h1 ->
      let s = B.deref h1 dst in
      not (B.g_is_null s) /\
      invariant h1 s /\

      B.(modifies (loc_buffer dst) h0 h1) /\ (
      let State _ _ _ initial_pn' aead_state' iv' hp_key' pn' ctr_state' = B.deref h1 s in
      aead_state' == aead_state /\
      ctr_state' == ctr_state /\
      B.(fresh_loc (loc_buffer iv') h0 h1) /\
      B.(fresh_loc (loc_buffer hp_key') h0 h1) /\
      B.(fresh_loc (loc_buffer pn') h0 h1) /\
      B.(fresh_loc (loc_addr_of_buffer s) h0 h1) /\

      G.reveal initial_pn' == U64.v initial_pn)))

#push-options "--z3rlimit 50"
let create_in_core i r dst initial_pn traffic_secret aead_state ctr_state =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;
  LowStar.ImmutableBuffer.recall label_iv;
  LowStar.ImmutableBuffer.recall_contents label_iv QUIC.Spec.label_iv;
  LowStar.ImmutableBuffer.recall label_hp;
  LowStar.ImmutableBuffer.recall_contents label_hp QUIC.Spec.label_hp;

  (**) let h0 = ST.get () in
  (**) assert_norm FStar.Mul.(8 * 12 <= pow2 64 - 1);

  // The modifies clauses that we will transitively carry across this function body.
  let mloc = G.hide (B.(loc_buffer dst `loc_union` loc_unused_in h0)) in
  let e_traffic_secret: G.erased (Spec.Hash.Definitions.bytes_hash i.hash_alg) =
    G.hide (B.as_seq h0 traffic_secret) in
  let e_initial_pn: G.erased QUIC.Spec.nat62 = G.hide (U64.v initial_pn) in

  let iv = B.malloc r 0uy 12ul in
  let hp_key = B.malloc r 0uy (key_len32 i.aead_alg) in
  let pn = B.malloc r initial_pn 1ul in
  (**) let h1 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h0 h1 loc_none);
  (**) assert (B.length hp_key = QUIC.Spec.ae_keysize i.aead_alg);

  let s: state_s i = State #i
    i.hash_alg i.aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state
  in

  let s:B.pointer_or_null (state_s i) = B.malloc r s 1ul in
  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);
  (**) B.(modifies_trans (G.reveal mloc) h0 h1 (G.reveal mloc) h2);

  derive_secret i.hash_alg iv 12uy traffic_secret label_iv 2uy;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer iv));
  (**) B.(modifies_trans (G.reveal mloc) h0 h2 (G.reveal mloc) h3);

  derive_secret i.hash_alg hp_key (key_len i.aead_alg) traffic_secret label_hp 2uy;
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer hp_key));
  (**) B.(modifies_trans (G.reveal mloc) h0 h3 (G.reveal mloc) h4);

  dst *= s;
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer dst));
  (**) B.(modifies_trans (G.reveal mloc) h0 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in (loc_buffer dst) h0 h5)
#pop-options

#push-options "--z3rlimit 256"
let create_in i r dst initial_pn traffic_secret =
  LowStar.ImmutableBuffer.recall label_key;
  LowStar.ImmutableBuffer.recall_contents label_key QUIC.Spec.label_key;

  (**) let h0 = ST.get () in

  push_frame ();
  (**) let h1 = ST.get () in
  let mloc = G.hide (B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst
    `loc_union` loc_unused_in h0)) in

  let aead_key = B.alloca 0uy (key_len32 i.aead_alg) in
  let aead_state: B.pointer (B.pointer_or_null (AEAD.state_s i.aead_alg)) =
    B.alloca B.null 1ul in
  let ctr_state: B.pointer (B.pointer_or_null (CTR.state_s (as_cipher_alg i.aead_alg))) =
    B.alloca (B.null #(CTR.state_s (as_cipher_alg i.aead_alg))) 1ul in
  let dummy_iv = B.alloca 0uy 12ul in

  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 (loc_none));

  derive_secret i.hash_alg aead_key (key_len i.aead_alg) traffic_secret label_key 3uy;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer aead_key));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let ret = AEAD.create_in #i.aead_alg r aead_state aead_key in
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer aead_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  let ret' = CTR.create_in (as_cipher_alg i.aead_alg) r ctr_state aead_key dummy_iv 12ul 0ul in
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer ctr_state));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);
  (**) B.(modifies_only_not_unused_in B.(loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h1 h5);

  match ret with
  | UnsupportedAlgorithm ->
      pop_frame ();
      (**) let h6 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

  match ret' with
  | UnsupportedAlgorithm ->
      pop_frame ();
      (**) let h6 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h5 h6);
      UnsupportedAlgorithm

  | Success ->

      let aead_state: AEAD.state i.aead_alg = !*aead_state in
      (**) assert (AEAD.invariant h5 aead_state);

      let ctr_state: CTR.state (as_cipher_alg i.aead_alg) = !*ctr_state in
      (**) assert (CTR.invariant h5 ctr_state);

      create_in_core i r dst initial_pn traffic_secret aead_state ctr_state;
      (**) let h6 = ST.get () in

      (**) B.(modifies_loc_includes
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst) h5 h6
        (loc_buffer dst));
      (**) B.(modifies_trans
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h1 h5
        (loc_region_only true (HS.get_tip h1) `loc_union` loc_buffer dst)
        h6);

      pop_frame ();
      (**) let h7 = ST.get () in
      (**) B.(modifies_fresh_frame_popped h0 h1 (loc_buffer dst) h6 h7);
      (**) frame_invariant (B.loc_region_only false (HS.get_tip h6)) (B.deref h7 dst) h6 h7;

      Success
#pop-options


let format_header (dst: B.buffer U8.t) (h: header) (npn: B.buffer U8.t) (pn_len: u2):
  Stack unit
    (requires (fun h0 ->
      B.length dst = QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) /\
      B.length npn = 1 + U8.v pn_len /\
      header_live h h0 /\
      header_disjoint h /\
      B.(all_disjoint [ loc_buffer dst; header_footprint h; loc_buffer npn ])))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\ (
      let fh = QUIC.Spec.format_header (g_header h h0) (B.as_seq h0 npn) in
      S.slice (B.as_seq h1 dst) 0 (S.length fh) `S.equal` fh)))
=
  admit ();
  C.Failure.failwith C.String.(!$"TODO")

let vlen (n:u62) : x:U8.t { U8.v x = QUIC.Spec.vlen (U64.v n) } =
  assert_norm (pow2 6 = 64);
  assert_norm (pow2 14 = 16384);
  assert_norm (pow2 30 = 1073741824);
  if n `U64.lt` 64UL then 1uy
  else if n `U64.lt` 16384UL then 2uy
  else if n `U64.lt` 1073741824UL then 4uy
  else 8uy

let header_len (h: header) (pn_len: u2): Stack U32.t
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    U32.v x = QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) /\
    h0 == h1)
=
  [@inline_let]
  let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32 in
  [@inline_let]
  let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64 in
  match h with
  | Short _ _ _ cid_len ->
      U32.(1ul +^ u32_of_u8 cid_len +^ 1ul +^ u32_of_u8 pn_len)
  | Long _ _ _ dcil _ scil plain_len ->
      assert_norm (pow2 32 < pow2 62);
      U32.(6ul +^ u32_of_u8 (add3 dcil) +^ u32_of_u8 (add3 scil) +^
        u32_of_u8 (vlen (u64_of_u32 plain_len)) +^ 1ul +^ u32_of_u8 pn_len)

let block_len (a: Spec.Agile.Cipher.cipher_alg):
  x:U32.t { U32.v x = Spec.Agile.Cipher.block_length a }
=
  let open Spec.Agile.Cipher in
  match a with | CHACHA20 -> 64ul | _ -> 16ul

#push-options "--z3rlimit 100"
inline_for_extraction
let block_of_sample (a: Spec.Agile.Cipher.cipher_alg)
  (dst: B.buffer U8.t)
  (s: CTR.state a)
  (k: B.buffer U8.t)
  (sample: B.buffer U8.t):
  Stack unit
    (requires fun h0 ->
      B.(all_live h0 [ buf dst; buf k; buf sample ]) /\
      CTR.invariant h0 s /\
      B.(all_disjoint
        [ CTR.footprint h0 s; loc_buffer dst; loc_buffer k; loc_buffer sample ]) /\
      Spec.Agile.Cipher.(a == AES128 \/ a == AES256 \/ a == CHACHA20) /\
      B.length k = Spec.Agile.Cipher.key_length a /\
      B.length dst = 16 /\
      B.length sample = 16)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst `loc_union` CTR.footprint h0 s) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        QUIC.Spec.block_of_sample a (B.as_seq h0 k) (B.as_seq h0 sample) /\
      CTR.footprint h0 s == CTR.footprint h1 s /\
      CTR.invariant h1 s)
=
  push_frame ();
  (**) let h0 = ST.get () in
  let zeroes = B.alloca 0uy (block_len a) in
  let dst_block = B.alloca 0uy (block_len a) in
  begin match a with
  | Spec.Agile.Cipher.CHACHA20 ->
      let ctr = LowStar.Endianness.load32_le (B.sub sample 0ul 4ul) in
      let iv = B.sub sample 4ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `S.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `S.equal` S.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul
  | _ ->
      let ctr = LowStar.Endianness.load32_be (B.sub sample 12ul 4ul) in
      let iv = B.sub sample 0ul 12ul in
      (**) let h1 = ST.get () in
      CTR.init (G.hide a) s k iv 12ul ctr;
      CTR.update_block (G.hide a) s dst_block zeroes;
      (**) let h2 = ST.get () in
      (**) seq_map2_xor0 (B.as_seq h1 dst_block)
      (**)   (Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      (**) assert (B.as_seq h2 dst_block `S.equal`
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr));
      let dst_slice = B.sub dst_block 0ul 16ul in
      (**) assert (B.as_seq h2 dst_slice `S.equal` S.slice (
      (**)   Spec.Agile.Cipher.ctr_block a (B.as_seq h0 k) (B.as_seq h1 iv) (U32.v ctr)
      (**) ) 0 16);
      B.blit dst_slice 0ul dst 0ul 16ul

  end;
  pop_frame ()
#pop-options

let pn_sizemask (dst: B.buffer U8.t) (pn_len: u2): Stack unit
  (requires fun h0 ->
    B.live h0 dst /\ B.length dst = 4)
  (ensures fun h0 _ h1 ->
    B.as_seq h1 dst `S.equal` QUIC.Spec.pn_sizemask (U8.v pn_len) /\
    B.(modifies (loc_buffer dst) h0 h1))
=
  let open FStar.Mul in
  [@ inline_let ]
  let pn_len32 = FStar.Int.Cast.uint8_to_uint32 pn_len in
  assert (U32.v pn_len32 = U8.v pn_len);
  assert_norm (0xffffffff = pow2 32 - 1);
  assert (24 - 8 * U32.v pn_len32 < 32);
  assert (24 - 8 * U32.v pn_len32 >= 0);
  FStar.UInt.shift_left_value_lemma #32 1 (24 - 8 * U32.v pn_len32);
  FStar.Math.Lemmas.pow2_lt_compat 32 (24 - 8 * U32.v pn_len32);
  FStar.Math.Lemmas.modulo_lemma (pow2 (24 - 8 * U32.v pn_len32)) (pow2 32);
  assert (U32.(v (1ul <<^ (24ul -^ 8ul *^ pn_len32))) = pow2 (24 - 8 * U32.v pn_len32));
  LowStar.Endianness.store32_be dst
    U32.(0xfffffffful -^ (1ul <<^ (24ul -^ 8ul *^ pn_len32)) +^ 1ul)

let g_hp_key #i h (s: state i) =
  B.as_seq h (State?.hp_key (B.deref h s))

let header_encrypt_pre
  (i: index)
  (dst:B.buffer U8.t)
  (dst_len:U32.t)
  (s:state i)
  (h:header)
  (cipher:G.erased QUIC.Spec.cbytes)
  (iv:G.erased (S.seq U8.t))
  (npn:B.buffer U8.t)
  (pn_len:u2)
  (h0: HS.mem)
=
  let h_len = QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) in

  // Administrative: memory
  B.(all_live h0 [ buf dst; buf s; buf npn ]) /\
  invariant h0 s /\
  B.(all_disjoint [ footprint h0 s; loc_buffer dst; loc_buffer npn ]) /\

  // Administrative: lengths
  B.length dst = U32.v dst_len /\
  U32.v dst_len = h_len + S.length (G.reveal cipher) /\
  S.length (G.reveal iv) = 12 /\
  B.length npn = 1 + U8.v pn_len /\ (

  // ``dst`` contains formatted header + ciphertext
  let h_seq = S.slice (B.as_seq h0 dst) 0 h_len in
  let c = S.slice (B.as_seq h0 dst) h_len (U32.v dst_len) in
  h_seq `S.equal` QUIC.Spec.format_header (g_header h h0) (B.as_seq h0 npn) /\
  c `S.equal` G.reveal cipher)

val header_encrypt: i:G.erased index -> (
  let i = G.reveal i in
  dst:B.buffer U8.t ->
  dst_len:U32.t ->
  s:state i ->
  h:header ->
  cipher:G.erased QUIC.Spec.cbytes ->
  iv:G.erased (S.seq U8.t) ->
  npn:B.buffer U8.t ->
  pn_len:u2 ->
  Stack unit
    (requires header_encrypt_pre i dst dst_len s h cipher iv npn pn_len)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer dst `loc_union` footprint_s #i h0 (B.deref h0 s)) h0 h1) /\
      B.as_seq h1 dst `S.equal`
        QUIC.Spec.header_encrypt i.aead_alg (g_hp_key h0 s) (g_header h h0)
          (B.as_seq h0 npn) (G.reveal cipher) /\
      invariant h1 s /\
      footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s)))


let pn_offset (h: header): Stack U32.t
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    U32.v x = QUIC.Spec.pn_offset (g_header h h0) /\ h0 == h1)
=
  (**) assert_norm (QUIC.Spec.max_cipher_length < pow2 62 /\ pow2 32 < pow2 62);
  [@inline_let] let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32 in
  [@inline_let] let u64_of_u32 = FStar.Int.Cast.uint32_to_uint64 in
  match h with
  | Short _ _ _ cid_len ->
      1ul `U32.add` u32_of_u8 cid_len
  | Long _ _ _ dcil _ scil pl ->
      6ul `U32.add` u32_of_u8 (add3 dcil) `U32.add` u32_of_u8 (add3 scil)
        `U32.add` u32_of_u8 (vlen (u64_of_u32 pl))


#push-options "--z3rlimit 1000"
let header_encrypt i dst dst_len s h cipher iv npn pn_len =
  let State _ aead_alg _ _ aead_state _ k _ ctr_state = !*s in
  // [@inline_let]
  let u32_of_u8 = FStar.Int.Cast.uint8_to_uint32 in
  (**) assert (U32.v dst_len >= 4);
  (**) let h0  = ST.get () in

  let pn_offset = pn_offset h in
  let h_len = header_len h pn_len in
  let sample = B.sub dst (h_len `U32.add` 3ul `U32.sub` u32_of_u8 pn_len) 16ul in
  let c = B.sub dst h_len (dst_len `U32.sub` h_len) in
  (**) assert (U32.v h_len = QUIC.Spec.header_len (g_header h h0) (U8.v pn_len));
  (**) assert (U32.v dst_len = U32.v h_len + S.length (G.reveal cipher));
  (**) lemma_slice (B.as_seq h0 dst) (U32.v h_len);
  (**) assert (B.as_seq h0 c `S.equal` G.reveal cipher);
  (**) assert (B.as_seq h0 sample `S.equal`
  (**)   S.slice (G.reveal cipher) (3 - U8.v pn_len) (19 - U8.v pn_len));

  push_frame ();
  let mask = B.alloca 0uy 16ul in
  let pn_mask = B.alloca 0uy 4ul in
  (**) let h1 = ST.get () in
  (**) assert (B.(loc_disjoint (loc_buffer pn_mask) (footprint h1 s)));
  (**) assert (B.(all_live h1 [ buf mask; buf k; buf sample ]));

  (**) assert (CTR.invariant h1 ctr_state);
  (**) assert (invariant h1 s);
  (**) assert (B.(all_disjoint
    [ CTR.footprint h1 ctr_state; loc_buffer k ]));

  block_of_sample (as_cipher_alg aead_alg) mask ctr_state k sample;
  (**) let h2 = ST.get () in
  (**) assert (CTR.footprint h1 ctr_state == CTR.footprint h2 ctr_state);
  (**) assert (AEAD.footprint h1 aead_state == AEAD.footprint h2 aead_state);

  pn_sizemask pn_mask pn_len;
  (**) let h3 = ST.get () in
  (**) frame_invariant B.(loc_buffer pn_mask) s h2 h3;

  let sub_mask = B.sub mask 1ul 4ul in
  (**) assert (B.as_seq h3 sub_mask `S.equal` S.slice (B.as_seq h3 mask) 1 5);
  op_inplace pn_mask 4ul sub_mask 4ul 0ul U8.logand;
  (**) pointwise_seq_map2 U8.logand (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask) 0;
  (**) and_inplace_commutative (B.as_seq h3 pn_mask) (B.as_seq h3 sub_mask);
  (**) pointwise_seq_map2 U8.logand (B.as_seq h3 sub_mask) (B.as_seq h3 pn_mask) 0;
  (**) let h4 = ST.get () in
  (**) frame_invariant B.(loc_buffer pn_mask) s h3 h4;
  (**) assert (invariant h4 s);
  (**) assert (B.(loc_disjoint (footprint h4 s) (loc_buffer dst)));
  let sflags = if Short? h then 0x1fuy else 0x0fuy in
  let fmask = mask.(0ul) `U8.logand` sflags in

  op_inplace dst dst_len pn_mask 4ul pn_offset U8.logxor;
  (**) let h5 = ST.get () in
  (**) frame_invariant B.(loc_buffer dst) s h4 h5;
  (**) assert (invariant h5 s);

  dst.(0ul) <- dst.(0ul) `U8.logxor` fmask;
  (**) let h6 = ST.get () in
  (**) frame_invariant B.(loc_buffer dst) s h5 h6;
  (**) assert (invariant h6 s);
  (**) upd_op_inplace U8.logxor (B.as_seq h5 dst) fmask;
  assert (
    let the_npn = npn in
    let open QUIC.Spec in
    let a = aead_alg in
    let k = B.as_seq h0 k in
    let h = g_header h h0 in
    let npn = B.as_seq h0 the_npn in
    let c = G.reveal cipher in
    B.as_seq h6 dst `S.equal` QUIC.Spec.header_encrypt aead_alg k h npn c);
  pop_frame ();
  (**) let h7 = ST.get () in
  ()


let tag_len (a: QUIC.Spec.ea): x:U32.t { U32.v x = Spec.Agile.AEAD.tag_length a /\ U32.v x = 16} =
  let open Spec.Agile.AEAD in
  match a with
  | CHACHA20_POLY1305 -> 16ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul

inline_for_extraction
let tricky_addition (aead_alg: QUIC.Spec.ea) (h: header) (pn_len: u2) (plain_len: U32.t {
    3 <= U32.v plain_len /\
    U32.v plain_len < QUIC.Spec.max_plain_length
  }):
  Stack U32.t
    (requires fun h0 -> header_live h h0)
    (ensures fun h0 x h1 ->
      h0 == h1 /\
      U32.v x = QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) + U32.v plain_len +
        Spec.Agile.AEAD.tag_length aead_alg)
=
  header_len h pn_len `U32.add` plain_len `U32.add` tag_len aead_alg

open FStar.Mul

val encrypt_core: #i:G.erased index -> (
  let i = G.reveal i in
  s:state i ->
  dst:B.buffer U8.t ->
  h:header ->
  plain: B.buffer U8.t ->
  plain_len: U32.t {
    3 <= U32.v plain_len /\
    U32.v plain_len < QUIC.Spec.max_plain_length /\
    B.length plain = U32.v plain_len
  } ->
  pn_len: u2 ->
  stack: G.erased B.loc ->
  pnb:B.buffer U8.t ->
  this_iv:B.buffer U8.t ->
  Stack unit
    (requires fun h0 ->
      assert_norm (pow2 62 < pow2 (8 * 12));
      let stack = G.reveal stack in
      // Memory & preservation
      B.(all_live h0 [ buf dst; buf plain; buf pnb; buf this_iv ]) /\
      header_live h h0 /\
      header_disjoint h /\
      B.(all_disjoint [ stack; footprint h0 s; loc_buffer dst;
        header_footprint h; loc_buffer plain ]) /\

      invariant h0 s /\

      // Local stuff
      B.(loc_includes stack (loc_buffer pnb)) /\
      B.(loc_includes stack (loc_buffer this_iv)) /\
      B.(disjoint pnb this_iv) /\
      B.length pnb = 12 /\
      B.length this_iv = 12 /\
      B.as_seq h0 pnb `S.equal`
        FStar.Endianness.n_to_be 12 (g_packet_number (B.deref h0 s) h0) /\

      incrementable s h0 /\ (
      let clen = U32.v plain_len + Spec.Agile.AEAD.tag_length i.aead_alg in
      let len = clen + QUIC.Spec.header_len (g_header h h0) (U8.v pn_len) in
      (Long? h ==> U32.v (Long?.plain_len h) = clen) /\
      B.length dst == len
    ))
    (ensures fun h0 r h1 ->
        // Memory & preservation
        B.(modifies (stack `loc_union`
          footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst)) h0 h1 /\
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
          QUIC.Spec.encrypt i.aead_alg k iv pne (U8.v pn_len) ctr (g_header h h0) plain)))

let encrypt_core #i s dst h plain plain_len pn_len stack pnb this_iv =
  (**) let h0 = ST.get () in
  (**) let m_loc = G.hide B.(G.reveal stack `loc_union`
  (**)   footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst) in
  (**) assert_norm (pow2 62 < pow2 (8 * 12));

  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state = !*s
  in
  let npn = B.sub pnb (11ul `U32.sub` u32_of_u8 pn_len) (1ul `U32.add` u32_of_u8 pn_len) in
  let dst_h = B.sub dst 0ul (header_len h pn_len) in
  let dst_ciphertag = B.sub dst (header_len h pn_len) (plain_len `U32.add` tag_len aead_alg) in
  let dst_cipher = B.sub dst_ciphertag 0ul plain_len in
  let dst_tag = B.sub dst_ciphertag plain_len (tag_len aead_alg) in

  format_header dst_h h npn pn_len;
  (**) let h1 = ST.get () in
  (**) frame_invariant B.(loc_buffer dst) s h0 h1;
  (**) assert (footprint_s h0 (B.deref h0 s) == footprint_s h1 (B.deref h1 s));
  (**) B.(modifies_loc_includes (G.reveal m_loc) h0 h1 (loc_buffer dst));
  (**) QUIC.Spec.lemma_format_len aead_alg (g_header h h0) (B.as_seq h1 npn);

  C.Loops.map2 this_iv pnb iv 12ul U8.logxor;
  (**) let h2 = ST.get () in
  (**) frame_invariant B.(loc_buffer this_iv) s h1 h2;
  (**) assert (footprint_s h1 (B.deref h1 s) == footprint_s h2 (B.deref h2 s));
  (**) B.(modifies_loc_includes (G.reveal m_loc) h1 h2 (loc_buffer this_iv));
  (**) B.(modifies_trans (G.reveal m_loc) h0 h1 (G.reveal m_loc) h2);
  (**) pointwise_seq_map2 U8.logxor (B.as_seq h1 pnb) (B.as_seq h1 iv) 0;
  (**) assert (
    let open QUIC.Spec in
    let npn: lbytes (1 + U8.v pn_len) = S.slice (B.as_seq h0 pnb) (11 - U8.v pn_len) 12 in
    let s0 = g_traffic_secret (B.deref h0 s) in
    let siv = derive_secret i.hash_alg s0 label_iv 12 in
    B.as_seq h2 this_iv `S.equal` xor_inplace (B.as_seq h0 pnb) siv 0
  );

  let l = header_len h pn_len in
  let r = AEAD.encrypt #(G.hide aead_alg) aead_state
    this_iv 12ul dst_h (header_len h pn_len) plain plain_len dst_cipher dst_tag in
  (**) let h3 = ST.get () in
  (**) assert (invariant h3 s);
  (**) assert (footprint_s h2 (B.deref h2 s) == footprint_s h2 (B.deref h3 s));
  (**) B.(modifies_loc_includes (G.reveal m_loc) h2 h3
    (AEAD.footprint h2 aead_state `loc_union` loc_buffer dst));
  (**) B.(modifies_trans (G.reveal m_loc) h0 h2 (G.reveal m_loc) h3);
  (**) assert (r = Success);
  (**) assert (
    let open QUIC.Spec in
    let s0 = g_traffic_secret (B.deref h0 s) in
    let siv = derive_secret i.hash_alg s0 label_iv 12 in
    let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
    let seqn = g_packet_number (B.deref h0 s) h0 in
    let h = g_header h h0 in
    let plain = B.as_seq h0 plain in
    let a = aead_alg in

    let pnb = FStar.Endianness.n_to_be 12 seqn  in
    let npn: lbytes (1 + U8.v pn_len) = S.slice pnb (11 - U8.v pn_len) 12 in
    let header = format_header h npn in
    let iv = xor_inplace pnb siv 0 in
    let cipher = Spec.Agile.AEAD.encrypt #a k iv header plain in
    cipher `S.equal` B.as_seq h3 dst_ciphertag
  );

  let dst_len = tricky_addition aead_alg h pn_len plain_len in
  let e_cipher = G.hide ((B.as_seq h3 dst_ciphertag) <: QUIC.Spec.cbytes) in
  let e_iv = G.hide (B.as_seq h3 this_iv) in
  header_encrypt i dst dst_len s h e_cipher e_iv npn pn_len;
  (**) let h4 = ST.get () in
  (**) assert (invariant h4 s);
  (**) assert (footprint_s h3 (B.deref h3 s) == footprint_s h4 (B.deref h4 s));
  (**) B.(modifies_loc_includes (G.reveal m_loc) h3 h4
    (footprint_s h3 (B.deref h3 s) `loc_union` loc_buffer dst));
  (**) B.(modifies_trans (G.reveal m_loc) h0 h3 (G.reveal m_loc) h4);
  (**) assert (
    let open QUIC.Spec in
    let s0 = g_traffic_secret (B.deref h0 s) in
    let siv = derive_secret i.hash_alg s0 label_iv 12 in
    let k = derive_secret i.hash_alg s0 label_key (Spec.Agile.AEAD.key_length i.aead_alg) in
    let seqn = g_packet_number (B.deref h0 s) h0 in
    let h = g_header h h0 in
    let plain = B.as_seq h0 plain in
    let a = aead_alg in
    let hpk = g_hp_key h0 s in
    let pn_len = U8.v pn_len in

    B.as_seq h4 dst `S.equal` QUIC.Spec.encrypt a k siv hpk pn_len seqn h plain
  )

#set-options "--z3rlimit 300"
let encrypt #i s dst h plain plain_len pn_len =
  (**) let h0 = ST.get () in
  let State hash_alg aead_alg e_traffic_secret e_initial_pn
    aead_state iv hp_key pn ctr_state = !*s
  in

  push_frame ();
  (**) let h1 = ST.get () in
  (**) let mloc = G.hide B.(loc_all_regions_from false (HS.get_tip h1) `loc_union`
    footprint_s h0 (deref h0 s) `loc_union` loc_buffer dst) in

  let pnb0 = B.alloca 0uy 16ul in
  let this_iv = B.alloca 0uy 12ul in
  (**) let h2 = ST.get () in
  (**) frame_invariant B.(loc_none) s h1 h2;
  (**) assert (footprint_s h1 (B.deref h1 s) == footprint_s h2 (B.deref h2 s));
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);

  let pn_: U64.t = !*pn in
  let pn128: FStar.UInt128.t = FStar.Int.Cast.Full.uint64_to_uint128 pn_ in
  LowStar.Endianness.store128_be pnb0 pn128;
  (**) let h3 = ST.get () in
  (**) frame_invariant B.(loc_buffer pnb0) s h2 h3;
  (**) assert (footprint_s h2 (B.deref h2 s) == footprint_s h3 (B.deref h3 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  let pnb = B.sub pnb0 4ul 12ul in
  (**) (
  (**) let open FStar.Endianness in
  (**) assert_norm (pow2 64 < pow2 (8 * 12));
  (**) calc (==) {
  (**)   be_to_n (B.as_seq h3 pnb);
  (**) (==) { }
  (**)   be_to_n (S.slice (B.as_seq h3 pnb0) 4 16);
  (**) (==) { be_to_n_slice (B.as_seq h3 pnb0) 4 }
  (**)   be_to_n (B.as_seq h3 pnb0) % pow2 (8 * 12);
  (**) (==) { FStar.Math.Lemmas.small_mod (U64.v pn_) (pow2 (8 * 12)) }
  (**)   be_to_n (B.as_seq h3 pnb0);
  (**) });
  (**) assert (B.as_seq h3 pnb `S.equal`
  (**)   FStar.Endianness.n_to_be 12 (g_packet_number (B.deref h0 s) h0));

  (**) assert B.(loc_disjoint (loc_region_only true (B.frameOf s))
  (**)   (loc_all_regions_from false (HS.get_tip h1)));
  encrypt_core #i s dst h plain plain_len pn_len
    (G.hide B.(loc_all_regions_from false (HS.get_tip h1))) pnb this_iv;

  (**) let h4 = ST.get () in
  (**) assert (invariant h4 s);
  (**) assert (footprint_s h3 (B.deref h3 s) == footprint_s h4 (B.deref h4 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  (**) assert_norm (pow2 62 < pow2 64);
  pn *= (pn_ `U64.add` 1UL);
  (**) let h5 = ST.get () in
  (**) assert (invariant h5 s);
  (**) assert (footprint_s h4 (B.deref h4 s) == footprint_s h5 (B.deref h5 s));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);

  pop_frame ();

  (**) let h6 = ST.get () in
  (**) frame_invariant B.(loc_all_regions_from false (HS.get_tip h1)) s h5 h6;
  (**) assert (footprint_s h5 (B.deref h5 s) == footprint_s h6 (B.deref h6 s));
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst `loc_union` footprint_s h0 (B.deref h0 s)) h5 h6;

  Success

/// Initial secrets
/// ---------------

// TODO: these three should be immutable buffers but we don't have const
// pointers yet for HKDF.
#push-options "--warn_error -272"
let initial_salt: initial_salt:B.buffer U8.t {
  B.length initial_salt = 20 /\
  B.recallable initial_salt
} =
  [@inline_let]
  let l = [
    0xc3uy; 0xeeuy; 0xf7uy; 0x12uy; 0xc7uy; 0x2euy; 0xbbuy; 0x5auy;
    0x11uy; 0xa7uy; 0xd2uy; 0x43uy; 0x2buy; 0xb4uy; 0x63uy; 0x65uy;
    0xbeuy; 0xf9uy; 0xf5uy; 0x02uy
  ] in
  assert_norm (List.Tot.length l = 20);
  B.gcmalloc_of_list HS.root l

let server_in: server_in:B.buffer U8.t {
  B.length server_in = 9 /\
  B.recallable server_in
} =
  [@inline_let]
  let l = [
    0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy; 0x69uy; 0x6euy
  ] in
  assert_norm (List.Tot.length l = 9);
  B.gcmalloc_of_list HS.root l

let client_in: client_in:B.buffer U8.t {
  B.length client_in = 9 /\
  B.recallable client_in
} =
  [@inline_let]
  let l = [
    0x63uy; 0x6cuy; 0x69uy; 0x65uy; 0x6euy; 0x74uy; 0x20uy; 0x69uy; 0x6euy
  ] in
  assert_norm (List.Tot.length l = 9);
  B.gcmalloc_of_list HS.root l
#pop-options

let initial_secrets dst_client dst_server cid cid_len =
  (**) let h0 = ST.get () in
  (**) B.recall initial_salt;
  (**) B.recall server_in;
  (**) B.recall client_in;
  assert_norm (Spec.Agile.Hash.(hash_length SHA2_256) = 32);

  push_frame ();
  (**) let h1 = ST.get () in
  (**) let mloc = G.hide (B.(loc_buffer dst_client `loc_union`
    loc_buffer dst_server `loc_union` loc_region_only true (HS.get_tip h1))) in

  let secret = B.alloca 0uy 32ul in
  (**) let h2 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h1 h2 loc_none);

  (**) hash_is_keysized_ Spec.Agile.Hash.SHA2_256;
  EverCrypt.HKDF.extract Spec.Agile.Hash.SHA2_256 secret initial_salt 20ul
    cid cid_len;
  (**) let h3 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h2 h3 (loc_buffer secret));
  (**) B.(modifies_trans (G.reveal mloc) h1 h2 (G.reveal mloc) h3);

  EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_client secret 32ul client_in 9ul 32ul;
  (**) let h4 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h3 h4 (loc_buffer dst_client));
  (**) B.(modifies_trans (G.reveal mloc) h1 h3 (G.reveal mloc) h4);

  EverCrypt.HKDF.expand Spec.Agile.Hash.SHA2_256 dst_server secret 32ul server_in 9ul 32ul;
  (**) let h5 = ST.get () in
  (**) B.(modifies_loc_includes (G.reveal mloc) h4 h5 (loc_buffer dst_server));
  (**) B.(modifies_trans (G.reveal mloc) h1 h4 (G.reveal mloc) h5);

  pop_frame ();
  (**) let h6 = ST.get () in
  (**) B.modifies_fresh_frame_popped h0 h1
  (**)   B.(loc_buffer dst_client `loc_union` loc_buffer dst_server) h5 h6

#push-options "--z3rlimit 50"
let parse_header (packet: B.buffer U8.t) (packet_len: U32.t) (cid_len: u4):
  Stack (option (header & U32.t & U32.t & u2))
    (requires (fun h0 ->
      B.live h0 packet /\
      B.length packet = U32.v packet_len /\
      21 <= B.length packet))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\ (
      let spec_result = QUIC.Spec.parse_header (B.as_seq h0 packet) (U8.v cid_len) in
      match r with
      | None -> QUIC.Spec.H_Failure? spec_result
      | Some (h, len, npn, pn_len) ->
          QUIC.Spec.H_Success? spec_result /\ (
          let QUIC.Spec.H_Success spec_npn spec_h _ = spec_result in
          U32.v npn == FStar.Endianness.be_to_n spec_npn /\
          U8.v pn_len = S.length spec_npn /\
          g_header h h1 == spec_h /\
          U32.v len == QUIC.Spec.header_len (g_header h h1) (U8.v pn_len) /\
          U32.v len <= U32.v packet_len /\

          // TR says: we'll need something more precise than this
          B.(loc_includes (loc_buffer packet) (header_footprint h))
          ))))
=
  admit ();
  C.Failure.failwith C.String.(!$"TODO")

val parse_varint (b: B.buffer U8.t) (len: U32.t):
  Stack (option (u62 & U32.t))
    (requires (fun h0 ->
      B.live h0 b /\
      B.length b = U32.v len))
    (ensures (fun h0 r h1 ->
      h0 == h1 /\ (

      let spec_result = QUIC.Spec.parse_varint (B.as_seq h0 b) in
      match r with
      | None -> None? spec_result
      | Some (x, ofs) ->
          Some? spec_result /\ (
          let Some (spec_val, spec_rest) = spec_result in
          U64.v x = spec_val /\
          U32.v ofs <= B.length b /\
          U32.v ofs = QUIC.Spec.vlen (U64.v x) /\
          S.slice (B.as_seq h0 b) (U32.v ofs) (B.length b) `S.equal`
            spec_rest))))
let parse_varint b len =
  admit ();
  C.Failure.failwith C.String.(!$"TODO")

val parse_long_header_clen (b: B.buffer U8.t) (len: U32.t):
  Stack (option (u4 & u4))
    (requires (fun h0 ->
      B.live h0 b /\
      B.length b = U32.v len))
    (ensures (fun h0 r h1 ->
      h0 == h1 /\ (

      let spec_result = QUIC.Spec.parse_long_header_clen (B.as_seq h0 b) in
      match r with
      | None -> None? spec_result
      | Some (dcil, scil) ->
          Some? spec_result /\ (
          let Some (spec_dcil, spec_scil, spec_rest) = spec_result in
          U8.v dcil == spec_dcil /\
          U8.v scil == spec_scil /\
          S.slice (B.as_seq h0 b) 1 (B.length b) `S.equal`
            spec_rest))))
let parse_long_header_clen b len =
  if len = 0ul then
    None
  else
    let x = b.(0ul) in
    Some (x `U8.div` 0x10uy, x `U8.rem` 0x10uy)

val long_sample (b: B.buffer U8.t) (len: U32.t):
  Stack (option (U32.t & U32.t))
    (requires (fun h0 ->
      B.live h0 b /\
      B.length b = U32.v len /\
      21 <= B.length b))
    (ensures (fun h0 r h1 ->
      h0 == h1 /\ (

      let spec_result = QUIC.Spec.long_sample (B.as_seq h0 b) in
      match r with
      | None -> None? spec_result
      | Some (sample_ofs, pn_ofs) ->
          Some? spec_result /\
          U32.v sample_ofs + 16 <= B.length b /\
          U32.v pn_ofs + 20 <= B.length b /\ (
          let Some (spec_sample, spec_pn_ofs) = spec_result in
          S.slice (B.as_seq h0 b) (U32.v sample_ofs) (U32.v sample_ofs + 16) `S.equal`
            spec_sample /\
          U32.v pn_ofs == spec_pn_ofs))))

#push-options "--z3rlimit 100"
let long_sample b b_len =
  let len5 = b_len `U32.sub` 5ul in
  let b5 = B.sub b 5ul len5 in
  match parse_long_header_clen b5 len5 with
  | Some (dcil, scil) ->
      let dcil_scil = U32.(u32_of_u8 (add3 dcil) +^ u32_of_u8 (add3 scil)) in
      if U32.(len5 -^ 1ul <^ dcil_scil) then
        None
      else
        let ofs = 6ul `U32.add` dcil_scil in
        match parse_varint (B.sub b ofs (b_len `U32.sub` ofs)) (b_len `U32.sub` ofs) with
        | None -> None
        | Some (len, ofs') ->
            assert (U32.v ofs' == QUIC.Spec.vlen (U64.v len));
            let pn_offset = U32.(ofs +^ ofs') in
            if U32.(pn_offset +^ 20ul <=^ b_len) then
              Some (pn_offset `U32.add` 4ul,
                6ul `U32.add` u32_of_u8 (add3 dcil) `U32.add` u32_of_u8 (add3 scil)
                `U32.add` ofs')
            else
              None
#pop-options

let bound_npn (pn_len: u2): x:U64.t { U64.v x == QUIC.Spec.bound_npn (U8.v pn_len) } =
  FStar.UInt.shift_left_value_lemma #64 1 (8 * (U8.v pn_len + 1));
  FStar.Math.Lemmas.pow2_le_compat 32 (8 * (U8.v pn_len + 1));
  FStar.Math.Lemmas.small_mod (pow2 (8 * (U8.v pn_len + 1))) (pow2 64);
  1UL `U64.shift_left` U32.(8ul *^ (u32_of_u8 pn_len +^ 1ul))

let p62: x:U64.t { U64.v x = pow2 62 } =
  assert_norm (pow2 62 = 4611686018427387904);
  4611686018427387904UL

let reduce_pn (pn_len: u2) (pn: u62):
  x:u62 { U64.v x == QUIC.Spec.reduce_pn (U8.v pn_len) (U64.v pn) }
=
  pn `U64.rem` bound_npn pn_len

let modulo_lt (a: nat) (b: pos): Lemma
  (ensures (a % b <= a))
=
  ()

let replace_modulo (a b new_mod: U64.t):
  Pure U64.t
    (requires
      U64.v b > 0 /\
      U64.(v new_mod < v b) /\
      QUIC.Spec.replace_modulo (U64.v a) (U64.v b) (U64.v new_mod) <= UInt.max_int 64)
    (ensures fun x ->
      U64.v x == QUIC.Spec.replace_modulo (U64.v a) (U64.v b) (U64.v new_mod))
=
  let open U64 in
  modulo_lt (U64.v a) (U64.v b);
  FStar.Math.Lemmas.modulo_range_lemma (U64.v a) (U64.v b);
  a -^ (a `rem` b) +^ new_mod

let in_window (pn_len: u2) (last: u62) (pn: u62):
  x:bool { b2t x <==> QUIC.Spec.in_window (U8.v pn_len) (U64.v last) (U64.v pn) }
=
  assert_norm (pow2 62 + 1 < pow2 64);
  assert_norm (pow2 62 - pow2 32 > 0);
  assert_norm (pow2 32 / 2 = pow2 31);
  let h = bound_npn pn_len in
  let open FStar.UInt64 in
  FStar.Math.Lemmas.pow2_le_compat 32 (8 * (U8.v pn_len + 1));
  (last +^ 1UL <^ h /^ 2UL && pn <^ h) ||
  (last +^ 1UL >=^ p62 -^ h /^ 2UL && pn >=^ p62 -^ h) ||
  (last +^ 1UL <^ pn +^ h /^ 2UL && pn <=^ last +^ 1UL +^ h /^ 2UL)

inline_for_extraction noextract
let expand_pn_ (pn_len: u2)
  (last: u62 { U64.v last < pow2 62 - 1 })
  (npn: u62 { U64.v npn < QUIC.Spec.bound_npn (U8.v pn_len) }):
  x:U64.t { U64.v x == QUIC.Spec.expand_pn (U8.v pn_len) (U64.v last) (U64.v npn) }
=
  let open U64 in
  (**) assert_norm (pow2 62 - 1 < pow2 64);
  let expected = last +^ 1UL in
  let bound = bound_npn pn_len in
  (**) QUIC.Spec.lemma_replace_modulo_bound (U64.v expected) (8 * (U8.v pn_len + 1))
  (**)   (U64.v npn) 64;
  let candidate = replace_modulo expected bound npn in
  (**) FStar.Math.Lemmas.pow2_le_compat 32 (8 * (U8.v pn_len + 1));
  (**) assert (U64.v candidate <= pow2 62 + pow2 32);
  (**) assert_norm (pow2 62 + pow2 32 + pow2 32 / 2 < pow2 64);
  (**) assert_norm (pow2 62 + pow2 32 < pow2 64);
  if candidate +^ bound /^ 2UL <=^ expected && candidate +^ bound <^ p62 then
    candidate +^ bound
  else if candidate >^ last +^ 1UL +^ bound /^ 2UL && candidate >=^ bound then
    candidate -^ bound
  else
    candidate

/// Note: rather than fight in the definition above to show that ``candidate``
/// (third case) is u62, we instead bail on that proof obligation, and rely on
/// the redefinition below to show it via the refinement that expand_pn computes
/// QUIC.Spec.expand_pn, which is shown to be a nat62.
let expand_pn (pn_len: u2)
  (last: u62 { U64.v last < pow2 62 - 1 })
  (npn: u62 { U64.v npn < QUIC.Spec.bound_npn (U8.v pn_len) }):
  x:u62 { U64.v x == QUIC.Spec.expand_pn (U8.v pn_len) (U64.v last) (U64.v npn) }
=
  expand_pn_ pn_len last npn


/// Start unverified
/// ----------------

let header_decrypt_pre (i:index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: u4)
  (h0: HS.mem)
=
  B.live h0 packet /\
  B.length packet == U32.v packet_len /\
  21 <= B.length packet

let header_decrypt_post (i:index)
  (s: state i)
  (packet: B.buffer U8.t)
  (packet_len: U32.t)
  (cid_len: u4)
  (h0: HS.mem)
  (r: (option (header & U32.t & U32.t & u2)))
  (h1: HS.mem): Ghost _
    (requires header_decrypt_pre i s packet packet_len cid_len h0)
    (ensures fun _ -> True)
=
  let a = i.aead_alg in
  let hpk = g_hp_key h0 s in
  let cid_len = U8.v cid_len in
  let spec_result = QUIC.Spec.header_decrypt a hpk cid_len (B.as_seq h0 packet) in
  match r with
  | None -> b2t (QUIC.Spec.H_Failure? spec_result)
  | Some (h, h_len, npn, pn_len) ->
      QUIC.Spec.H_Success? spec_result /\ (
      let QUIC.Spec.H_Success spec_npn spec_h _ = spec_result in
      U32.v npn == FStar.Endianness.be_to_n spec_npn /\
      U8.v pn_len = S.length spec_npn /\
      g_header h h1 == spec_h /\
      U32.v h_len == QUIC.Spec.header_len (g_header h h1) (U8.v pn_len) /\
      U32.v h_len <= U32.v packet_len /\

      B.(modifies (loc_buffer (gsub packet 0ul h_len) `loc_union`
        footprint_s h0 (B.deref h0 s)) h0 h1))

val header_decrypt_core: i:index ->
  (s: state i) ->
  (packet: B.buffer U8.t) ->
  (packet_len: U32.t) ->
  (cid_len: u4) ->
  (is_short: bool) ->
  (sample_offset: U32.t) ->
  (pn_offset: U32.t) ->
  Stack (option (header & U32.t & U32.t & u2))
    (requires fun h0 ->
      header_decrypt_pre i s packet packet_len cid_len h0 /\
      U32.v sample_offset + 16 <= U32.v packet_len /\
      U32.v pn_offset + 20 <= U32.v packet_len /\
      True) // TODO: tie together is_short, sample_offset and pn_offset
    (ensures (fun h0 r h1 ->
      header_decrypt_post i s packet packet_len cid_len h0 r h1))

#set-options "--admit_smt_queries true"
let header_decrypt_core i s packet packet_len cid_len is_short sample_offset pn_offset =
  let State _ aead_alg _ _ aead_state _ k _ ctr_state = !*s in

  push_frame ();
  let mask = B.alloca 0uy 16ul in
  let pn_mask = B.alloca 0uy 4ul in
  block_of_sample (as_cipher_alg i.aead_alg) mask ctr_state k (B.sub packet sample_offset 16ul);
  let sflags = if is_short then 0x1Fuy else 0x0fuy in
  let flags = packet.(0ul) `U8.logxor` (mask.(0ul) `U8.logand` sflags) in
  packet.(0ul) <- flags;
  let pn_len = flags `U8.rem` 4uy in
  pn_sizemask pn_mask pn_len;
  op_inplace (B.sub mask 1ul 4ul) 4ul pn_mask 4ul 0ul U8.logand;
  op_inplace packet packet_len pn_mask 4ul pn_offset U8.logxor;
  let r = parse_header packet packet_len cid_len in
  pop_frame ();
  r


val header_decrypt: i:index ->
  (s: state i) ->
  (packet: B.buffer U8.t) ->
  (packet_len: U32.t) ->
  (cid_len: u4) ->
  Stack (option (header & U32.t & U32.t & u2))
    (requires (fun h0 ->
      B.live h0 packet /\
      B.length packet = U32.v packet_len /\
      21 <= B.length packet))
    (ensures (fun h0 r h1 ->
      let a = i.aead_alg in
      let hpk = g_hp_key h0 s in
      let cid_len = U8.v cid_len in
      let spec_result = QUIC.Spec.header_decrypt a hpk cid_len (B.as_seq h0 packet) in
      match r with
      | None -> QUIC.Spec.H_Failure? spec_result
      | Some (h, h_len, npn, pn_len) ->
          QUIC.Spec.H_Success? spec_result /\ (
          let QUIC.Spec.H_Success spec_npn spec_h _ = spec_result in
          U32.v npn == FStar.Endianness.be_to_n spec_npn /\
          U8.v pn_len = S.length spec_npn /\
          g_header h h1 == spec_h /\
          U32.v h_len == QUIC.Spec.header_len (g_header h h1) (U8.v pn_len) /\
          U32.v h_len <= U32.v packet_len /\

          B.(modifies (loc_buffer (gsub packet 0ul h_len)) h0 h1)
          )))

let header_decrypt i s packet packet_len cid_len =
  let is_short = U8.(packet.(0ul) `U8.lt` 128uy) in
  match (
    if is_short then
      let offset = 5ul `U32.add` u32_of_u8 (add3 cid_len) in
      if U32.(offset +^ 16ul <=^ packet_len) then
        Some (offset, offset `U32.sub` 4ul)
      else
        None
    else
      long_sample packet packet_len
  ) with
  | None -> None
  | Some (sample_offset, pn_offset) ->
      header_decrypt_core i s packet packet_len cid_len is_short sample_offset pn_offset

let if_i_dont_write_this_i_get_a_pattern_warning (h: header) (h_len tag_len packet_len: U32.t): U32.t =
  match h with
  | Short _ _ _ _ -> packet_len `U32.sub` h_len `U32.sub` tag_len
  | Long _ _ _ _ _ _ ciphertag_len -> ciphertag_len `U32.sub` tag_len

let decrypt #i s dst packet packet_len cid_len =
  match parse_header packet packet_len cid_len with
  | None -> DecodeError
  | Some (h, h_len, npn, pn_len) ->
      let State hash_alg aead_alg _ initial_pn aead_state iv hp_key last_pn _ = !*s in
      let why_oh_why_these_let_bindings_all_the_time = !*last_pn in
      let pn = expand_pn pn_len why_oh_why_these_let_bindings_all_the_time (u64_of_u32 npn) in

      push_frame ();
      let pn_buf0 = B.alloca 0uy 12ul in
      let npn_buf = B.alloca 0uy 4ul in
      LowStar.Endianness.store128_be pn_buf0 (FStar.Int.Cast.Full.uint64_to_uint128 pn);
      let pn_buf = B.sub pn_buf0 4ul 12ul in
      LowStar.Endianness.store32_be npn_buf npn;
      op_inplace pn_buf 12ul iv 12ul 0ul U8.logxor;
      let is_short = U8.(packet.(0ul) `U8.lt` 128uy) in
      let tag_len = tag_len aead_alg in
      let cipher_len = if_i_dont_write_this_i_get_a_pattern_warning h h_len tag_len packet_len in
      let h_len: U32.t = h_len in
      let ad = B.sub packet 0ul h_len in
      let plain = B.sub packet h_len cipher_len in
      let tag = B.sub packet (h_len `U32.add` cipher_len) tag_len in
      match AEAD.decrypt #(G.hide aead_alg) aead_state iv 12ul ad h_len
        plain cipher_len
        tag
        plain
      with
      | AuthenticationFailure ->
          pop_frame ();
          AuthenticationFailure
      | Success ->
          pop_frame ();
          dst *= ({
            pn_len = pn_len;
            pn = pn;
            header = h;
            header_len = h_len;
            plain_len = cipher_len;
            total_len = h_len `U32.add` cipher_len `U32.add` tag_len
          });
          if pn `U64.gt` why_oh_why_these_let_bindings_all_the_time then
            last_pn *= pn;
          Success
