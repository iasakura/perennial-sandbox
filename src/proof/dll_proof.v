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

(* l points to a dlist node whose prev pointer is p and the last next pointer is n *)
Fixpoint is_dlist_node (l :  loc) (p : loc) (last : loc) (xs : list w64) : iProp Σ :=
  match xs with
  | [] => ⌜l = last⌝
  | v :: xs =>
    ∃ (n : loc),
      "Hl" ∷ ⌜l ≠ null ⌝ ∗
      "Hnext" ∷ l.[dll.Node.t, "next"] ↦ n ∗
      "Hprev" ∷ l.[dll.Node.t, "prev"] ↦ p ∗
      "His_dlist" ∷ is_dlist_node n l last xs
  end.

Definition own_list (l : loc) (xs : list w64) : iProp Σ :=
  ∃ (hd tl : loc),
    "Hhead" ∷ l.[dll.List.t, "head"] ↦ hd ∗
    "His_dlist" ∷ is_dlist_node hd null null xs ∗
    "Htail" ∷ l.[dll.List.t, "tail"] ↦ tl ∗
    "Hsize" ∷ l.[dll.List.t, "size"] ↦ (W64 (length xs)).

Lemma wp_Len (l : loc) (xs : list w64) :
  {{{ is_pkg_init dll ∗ own_list l xs }}}
    l @! (go.PointerType dll.List) @! "Len" #()
  {{{ RET #(W64 (length xs)); own_list l xs }}}.
Proof.
  wp_start as "Hown". iNamed "Hown".
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

Fixpoint Sorted (xs : list w64) :=
  match xs with
  | [] => True
  | x :: xs => match xs with
    | [] => True
    | y :: _ => (uint.Z x < uint.Z y ∧ Sorted xs)
    end
  end.

(* TODO: postcond should  intuitively denote xs = ys ++ y ++ z ++ zs and y < v < z with some side conditions for when they may be null*)
Lemma t (l p last : loc) (v : w64) (xs : list w64):
  {{{ is_pkg_init dll ∗ is_dlist_node l p last xs ∗ ⌜Sorted xs⌝ }}}
    l @! (go.PointerType dll.Node) @! "findLeastGreaterNode" (# v)
  {{{ prev node, RET #(prev, node); emp }}}.
Proof.
Abort.

Theorem insertSorted_spec  (l : loc) (xs : list w64) (v : w64) :
  {{{ is_pkg_init dll ∗ own_list l xs ∗ ⌜ Sorted xs ⌝  }}}
    l @! (go.PointerType dll.List) @! "InsertSorted" #v
  {{{ RET #(); ∃ ys zs, ⌜xs = ys ++ zs ⌝ ∗ ⌜Sorted (ys ++ v :: zs)⌝ ∗ own_list l (ys ++ v :: zs)}}}.
Proof.
  wp_start as "[Hown %HSorted]".
  iNamed "Hown".
  wp_auto.
  wp_if_destruct.
  - wp_alloc l' as "Hl".
    wp_auto.
    iApply "HΦ".
    iAssert (⌜xs = []⌝)%I as "->".
    { destruct xs as [|x xs]; [by done|].
      simpl.
      iDestruct "His_dlist" as "(%n & Hown)".
      iNamedSuffix "Hown" "Node".
      by iDestruct "HlNode" as "%HlNode".
    }
    iExists [], [].
    iSplitR; [by done|].
    iSplitR; [by done|].
    rewrite /own_list.
    iExists l', l'.
    simpl.
    iFrame.
    iPoseProof (typed_pointsto_not_null l' {| dll.Node.val' := v; dll.Node.next' := null; dll.Node.prev' := null |} with "[$Hl]") as "%Hl".
    iSplitL "".
    + by iPureIntro.
    + iStructNamed "Hl".
      simpl.
      iFrame.
  -
Admitted.

Print is_dlist_node.

End proof.

