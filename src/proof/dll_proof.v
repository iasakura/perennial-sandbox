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
Fixpoint is_dlist_node (l last prev next : loc) (xs : list w64) : iProp Σ :=
  match xs with
  (* for ensuring that traversal is immediately finished when xs = [] *)
  | [] => ⌜l = next ∧ last = prev⌝
  (* | [x] =>
    "Hl" ∷ ⌜l = last⌝ ∗
    "Hnext" ∷ l.[dll.Node.t, "next"] ↦ next ∗
    "Hprev" ∷ l.[dll.Node.t, "prev"] ↦ prev ∗
    "Hx" ∷ l.[dll.Node.t, "x"] ↦ x *)
  | v :: xs =>
    ∃ (n : loc),
      "Hl" ∷ ⌜l ≠ null⌝ ∗
      "Hval" ∷ l.[dll.Node.t, "val"] ↦ v ∗
      "Hnext" ∷ l.[dll.Node.t, "next"] ↦ n ∗
      "Hprev" ∷ l.[dll.Node.t, "prev"] ↦ prev ∗
      "His_dlist" ∷ is_dlist_node n last l next xs ∗
      "Hx" ∷ l.[dll.Node.t, "x"] ↦ v
  end.

Definition own_list (l : loc) (xs : list w64) : iProp Σ :=
  ∃ (hd tl : loc),
    "Hhead" ∷ l.[dll.List.t, "head"] ↦ hd ∗
    "His_dlist" ∷ is_dlist_node hd tl null null xs ∗
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

Lemma is_dlist_node_app fst last prev next xs ys :
  is_dlist_node fst last prev next (xs ++ ys)
  ⊣⊢
  ∃ mid_last mid_fst,
    is_dlist_node fst mid_last prev mid_fst xs ∗ is_dlist_node mid_fst last mid_last next ys.
Proof.
  revert fst prev.
  elim xs => [|x xs'].
  - move => fst prev.
    simpl.
    iSplit.
    + iIntros "H".
      iExists prev, fst.
      by iFrame.
    + iIntros  "(%mid_last & %mid_fst & [-> ->] & Hlst)".
      by iFrame.
  - move => IH fst prev.
    iSplit.
    + simpl.
      iIntros "[%n H]".
      iNamed "H".
      iPoseProof (IH n fst) as "H".
      iApply "H" in "His_dlist".
      iDestruct "His_dlist" as "(%mid_last & %mid_fst & Hfst & Hlst)".
      iExists mid_last, mid_fst.
      iFrameNamed.
      iSplitR "Hlst"; [|by done].
      iExists n.
      by iFrameNamed.
    + simpl.
      iIntros "(%mid_last & %mid_fst & (%n & Hfst) & Hlst)".
      iNamed "Hfst".
      iExists n.
      iFrameNamed.
      iApply IH.
      iExists mid_last, mid_fst.
      by iFrame.
Qed.

Lemma is_dlist_node_null_nil last prev next xs :
  is_dlist_node null last prev next xs -∗ ⌜xs = []⌝.
Proof.
  iIntros "H".
  case xs => [|x xs'].
  - by auto.
  - simpl.
    iDestruct "H" as "(%n & H)".
    iNamed "H".
    by iDestruct "Hl" as "%Hl".
Qed.

Lemma is_dlist_node_not_null_cons fst last prev xs :
  fst ≠ null ->
  is_dlist_node fst last prev null xs -∗
  ∃x xs', ⌜xs = x :: xs'⌝.
Proof.
  move => H.
  iIntros "H".
  case xs => [|x xs'].
  - simpl.
    by iDestruct "H" as "[-> ->]".
  - by iExists x, xs'.
Qed.

(* TODO: postcond should  intuitively denote xs = ys ++ y ++ z ++ zs and y < v < z with some side conditions for when they may be null*)
Lemma t (l last : loc) (v : w64) (xs : list w64):
  {{{ is_pkg_init dll ∗ is_dlist_node l last null null xs ∗ ⌜Sorted xs⌝ }}}
    l @! (go.PointerType dll.Node) @! "findLeastGreaterNode" (# v)
  {{{ prev node, RET (#prev, #node); ∃ ys zs,
        ⌜xs = ys ++ zs ∧ Sorted(ys ++ v :: zs)⌝ ∗
        is_dlist_node l prev null node ys ∗
        is_dlist_node node last prev null zs }}}.
Proof.
  wp_start as "[His_dlist HSorted]".
  wp_auto.
  iAssert (∃ ys zs (cur p : loc),
    ⌜xs = ys ++ zs ∧ ∀y, y ∈ ys -> uint.Z y ≤ uint.Z v⌝ ∗
    cur_ptr ↦ cur ∗ p_ptr ↦ p ∗
    is_dlist_node l p null cur ys ∗
    is_dlist_node cur last p null zs
  )%I with "[His_dlist p cur]" as "IH".
  {
    iExists [], xs, l, null.
    iFrame.
    iPureIntro.
    split.
    - split; first by done.
      move => y Hy.
      rewrite elem_of_nil in Hy.
      done.
    - by done.
  }
  wp_for.
  iDestruct "IH" as "(%ys & %zs & %cur & %p & [-> %Hyv] & Hcur & Hp & Hdlist_ys & Hdlist_zs)".
  wp_auto.
  (* rewrite -bool_decide_not. *)
  wp_if_destruct.
  - iApply "HΦ".
    iExists ys, zs.
    iAssert (⌜zs = []⌝)%I as "->".
    {
      by iApply is_dlist_node_null_nil in "Hdlist_zs".
    }
    iFrame.
    admit.
  - case zs => [|z zs'].
    + simpl.
      by iDestruct "Hdlist_zs" as "[-> ->]".
    + simpl.
      iDestruct "Hdlist_zs" as "(%n' & H)". iNamed "H".
      wp_auto.
      wp_if_destruct.
      * wp_for_post.
        iFrameNamed.
        iExists (ys ++ [z]), zs', n', cur.
        iSplitR.
        -- iPureIntro.
           split.
           ++ by rewrite -app_assoc.
           ++ intros y Hy.
              rewrite elem_of_app in Hy.
              case Hy => [Hy' | Hy'].
              ** by apply Hyv.
              ** admit.
        -- iFrame.
           admit.
      * iApply "HΦ".
        admit.
Admitted.

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

