module QUIC.Spec
include QUIC.Parse

module S = FStar.Seq
module HD = Spec.Hash.Definitions
module AEAD = Spec.Agile.AEAD

// JP: should we allow inversion on either hash algorithm or AEAD algorithm?
#set-options "--max_fuel 0 --max_ifuel 0"

let supported_hash = function
  | HD.SHA1 | HD.SHA2_256 | HD.SHA2_384 | HD.SHA2_512 -> true
  | _ -> false

let supported_aead = function
  | AEAD.AES128_GCM | AEAD.AES256_GCM | AEAD.CHACHA20_POLY1305 -> true
  | _ -> false

type ha = a:HD.hash_alg{supported_hash a}
type ea = a:AEAD.alg{supported_aead a}

// Move from Hashing.Spec to Spec.Hash?
let keysized (a:ha) (l:nat) =
  l <= HD.max_input_length a /\ l + HD.block_length a < pow2 32
let hashable (a:ha) (l:nat) = l <= HD.max_input_length a

// AEAD plain and ciphertext. We want to guarantee that regardless
// of the header size (max is 54), the neader + ciphertext + tag fits in a buffer
// JP: perhaps cleaner with a separate lemma; any reason for putting this in a refinement?
let max_plain_length: n:nat {
  forall a. {:pattern AEAD.max_length a} n <= AEAD.max_length a
} =
  pow2 32 - 70

let max_cipher_length : n:nat {
  forall a. {:pattern AEAD.max_length a \/ AEAD.tag_length a }
    n <= AEAD.max_length a + AEAD.tag_length a
} =
  pow2 32 - 54

type pbytes = b:bytes{let l = S.length b in 3 <= l /\ l < max_plain_length}
type cbytes = b:bytes{let l = S.length b in 19 <= l /\ l < max_cipher_length}

// JP: this is Spec.Agile.Cipher.key_length
let ae_keysize (a:ea) =
  match a with
  | AEAD.AES128_GCM -> 16
  | _ -> 32

// Static byte sequences to be fed into secret derivation. Marked as inline, so
// that they can be used as arguments to gcmalloc_of_list for top-level arrays.
inline_for_extraction
val label_key: lbytes 3
inline_for_extraction
val label_iv: lbytes 2
inline_for_extraction
val label_hp: lbytes 2

val derive_secret:
  a: ha ->
  prk:Spec.Hash.Definitions.bytes_hash a ->
  label: bytes ->
  len: nat ->
  Pure (lbytes len)
  (requires len <= 255 /\
    S.length label <= 244 /\
    keysized a (S.length prk)
    )
  (ensures fun out -> True)

type nat2 = n:nat{n < 4}
type nat4 = n:nat{n < 16}
type nat32 = n:nat{n < pow2 32}
type nat62 = n:nat{n < pow2 62}

let add3 (n:nat4) : n:nat{n=0 \/ (n >= 4 /\ n <= 18)} = if n = 0 then 0 else 3+n
let sub3 (n:nat{n = 0 \/ (n >= 4 /\ n <= 18)}) : nat4 = if n = 0 then 0 else n-3
type qbytes (n:nat4) = lbytes (add3 n)

// JP: seems appropriate for this module...?
let _: squash (inversion header) = allow_inversion header

// Header protection only
val header_encrypt: a:ea ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  c: cbytes ->
  GTot bytes // packet

// Note that cid_len cannot be parsed from short headers
val header_decrypt: a:ea ->
  hpk: lbytes (ae_keysize a) ->
  cid_len: nat ->
  p: bytes -> // packet
  GTot h_result

module P = QUIC.Parse

// This is just functional correctness, but does not guarantee security:
// decryption can succeed on an input that is not the encryption
// of the same arguments (see QUIC.Spec.Old.*_malleable)
val lemma_header_encryption_correct:
  a:ea ->
  k:lbytes (ae_keysize a) ->
  h:header { ~ (is_retry h) } ->
  c: cbytes (* {MLong? h ==> S.length c = MLong?.len h} *) ->
  Lemma (
    header_decrypt a k (dcid_len h) (header_encrypt a k h c)
    == H_Success h c)

noeq
type result =
| Success: 
  h: header ->
  plain: pbytes ->
  result
| Failure

val encrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  h: header ->
  plain: pbytes (* {Long? h ==> Long?.len h == S.length plain + AEAD.tag_length a} *) ->
  packet



/// compression of the packet number


let bound_npn (pn_len:nat2) = pow2 (8 `op_Multiply` (pn_len+1))

let in_window (pn_len:nat2) (last pn:nat) =
  let h = bound_npn pn_len in
  (last+1 < h/2 /\ pn < h) \/
  (last+1 >= pow2 62 - h/2 /\ pn >= pow2 62 - h) \/
  (last+1 - h/2 < pn /\ pn <= last+1 + h/2)

val reduce_pn :
  pn_len:nat2 ->
  pn:nat62 ->
  npn:nat{npn < bound_npn pn_len}

val expand_pn :
  pn_len:nat2 ->
  last:nat{last+1 < pow2 62} ->
  npn:nat{npn < bound_npn pn_len} ->
  pn:nat62{in_window pn_len last pn /\ pn % bound_npn pn_len = npn}

val lemma_parse_pn_correct : pn_len:nat2 -> last:nat{last+1 < pow2 62} -> pn:nat62 -> Lemma
  (requires in_window pn_len last pn)
  (ensures expand_pn pn_len last (reduce_pn pn_len pn) = pn)



/// decryption and correctness

val decrypt:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  static_iv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  last: nat{last+1 < pow2 62} ->
  cid_len: nat ->
  packet: packet ->
  result

val lemma_encrypt_correct:
  a: ea ->
  k: lbytes (AEAD.key_length a) ->
  siv: lbytes 12 ->
  hpk: lbytes (ae_keysize a) ->
  last: nat{last+1 < pow2 62} ->
  h: header ->
  p: pbytes (* {Long? h ==> Long?.len h == S.length p + AEAD.tag_length a} *) -> Lemma
  (requires True) // in_window pn_len last pn)
  (ensures
    decrypt a k siv hpk last (dcid_len h)
      (encrypt a k siv hpk h p)
    == Success h p)
