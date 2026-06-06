(* Proofs about the doubly-linked list in dll/list.go.
   Kept in its own package `dll` so the generated struct names (List/Node)
   resolve cleanly — the `example` package identifier collides with Coq's
   module resolution and made `example.List.t` unreferenceable from here.

   Following the elimination_stack proof style: describe the List struct with
   per-field points-to via the `l.[Struct.t, "field"]` notation. own_list tracks
   the size field against a logical list; the head/tail node chain is held
   abstractly (a full prev/next invariant is left as a heavier next step). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.perennial_sandbox Require Import dll.
From New.generatedproof.github_com.iasakura.perennial_sandbox Require Import dll.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : dll.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) dll := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) dll := build_get_is_pkg_init_wf.

Definition own_list (l : loc) (xs : list w64) : iProp Σ :=
  ∃ (hd tl : loc),
    "Hhead" ∷ l.[dll.List.t, "head"] ↦ hd ∗
    "Htail" ∷ l.[dll.List.t, "tail"] ↦ tl ∗
    "Hsize" ∷ l.[dll.List.t, "size"] ↦ (W64 (length xs)).

Lemma wp_Len (l : loc) (xs : list w64) :
  {{{ is_pkg_init dll ∗ own_list l xs }}}
    l @! (go.PointerType dll.List) @! "Len" #()
  {{{ RET #(W64 (length xs)); own_list l xs }}}.
Proof.
  wp_start as "Hown". iNamed "Hown".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

End proof.
