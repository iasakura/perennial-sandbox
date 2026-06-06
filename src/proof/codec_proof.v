(* wp specs for codec/codec.go: the actual program proof of encoding a message
   into wire bytes using tchajed/marshal. We use marshal's wp_WriteInt /
   wp_ReadInt directly (they are Admitted upstream in this checkout, but that
   just means we trust the marshal library — the structure of the proof is the
   real thing). *)
From New.proof Require Import proof_prelude.
From New.proof Require Import github_com.tchajed.marshal.
From New.code.github_com.iasakura.perennial_sandbox Require Import codec.
From New.generatedproof.github_com.iasakura.perennial_sandbox Require Import codec.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : codec.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) codec := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) codec := build_get_is_pkg_init_wf.

(* Encode p produces a fresh byte slice holding exactly the wire encoding
   u64_le A ++ u64_le B. *)
Lemma wp_Encode (a b : w64) :
  {{{ is_pkg_init codec }}}
    @! codec.Encode (#(codec.Pair.mk a b))
  {{{ (s : slice.t), RET #s;
      s ↦*{DfracOwn 1} (u64_le a ++ u64_le b) ∗ own_slice_cap w8 s (DfracOwn 1) }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iDestruct (own_slice_nil (DfracOwn 1) (V:=w8)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=w8)) as "Hcapnil".
  wp_apply (wp_WriteInt with "[$Hnil $Hcapnil]") as "%s1 [Hs1 Hcap1]".
  wp_apply (wp_WriteInt with "[$Hs1 $Hcap1]") as "%s2 [Hs2 Hcap2]".
  iApply "HΦ". iFrame.
Qed.

(* Decode parses two ints back out of a slice holding u64_le a ++ u64_le b,
   recovering exactly Pair{a, b}. *)
Lemma wp_Decode (s : slice.t) (a b : w64) dq :
  {{{ is_pkg_init codec ∗ s ↦*{dq} (u64_le a ++ u64_le b) }}}
    @! codec.Decode #s
  {{{ RET #(codec.Pair.mk a b); True }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  (* first ReadInt: prefix u64_le a, tail (u64_le b) *)
  wp_apply (wp_ReadInt with "[$Hs]") as "%s1 Hs1".
  (* second ReadInt: the tail is exactly u64_le b = u64_le b ++ [] *)
  rewrite -(app_nil_r (u64_le b)).
  wp_apply (wp_ReadInt with "[$Hs1]") as "%s2 Hs2".
  iApply "HΦ". done.
Qed.

End proof.
