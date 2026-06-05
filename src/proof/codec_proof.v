(* Encoding/decoding spec for codec/codec.go, at the byte-list level.

   The Go code (Encode/Decode) calls tchajed/marshal's WriteInt/ReadInt, whose
   wp specs are currently Admitted in this Perennial checkout — so we don't
   prove the program wp here. Instead we prove the *encoding* is well-defined
   and invertible, which is the mathematical heart of "parse bytes back into a
   struct": this is exactly how marshal itself specifies encodings
   (uint64_has_encoding / encodes), built on the trusted u64_le primitive. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.perennial_sandbox Require Import codec.
From New.generatedproof.github_com.iasakura.perennial_sandbox Require Import codec.

Section spec.

(* The wire encoding of a Pair: field A then field B, each little-endian u64. *)
Definition pair_has_encoding (bs : list u8) (a b : w64) : Prop :=
  bs = u64_le a ++ u64_le b.

(* Decoding is unambiguous: a byte string encodes at most one Pair.
   This is the round-trip guarantee — Decode (Encode p) can only be p. *)
Lemma pair_encoding_inj bs a1 b1 a2 b2 :
  pair_has_encoding bs a1 b1 ->
  pair_has_encoding bs a2 b2 ->
  a1 = a2 /\ b1 = b2.
Proof.
  rewrite /pair_has_encoding. intros H1 H2.
  rewrite H1 in H2.
  (* both 8-byte prefixes are u64_le, so app_inj_1 splits cleanly *)
  apply app_inj_1 in H2 as [HA HB].
  2:{ rewrite !u64_le_length //. }
  split.
  - by apply (inj u64_le).
  - by apply (inj u64_le).
Qed.

(* The encoded length is always 16 bytes, regardless of contents — the kind of
   framing fact a length-prefixed network reader relies on. *)
Lemma pair_encoding_length bs a b :
  pair_has_encoding bs a b -> length bs = 16%nat.
Proof.
  rewrite /pair_has_encoding => ->.
  rewrite length_app !u64_le_length //.
Qed.

End spec.
