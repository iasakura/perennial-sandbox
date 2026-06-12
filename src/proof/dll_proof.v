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
  | v :: xs =>
    ∃ (n : loc),
      "Hl" ∷ ⌜l ≠ null⌝ ∗
      "Hval" ∷ l.[dll.Node.t, "val"] ↦ v ∗
      "Hnext" ∷ l.[dll.Node.t, "next"] ↦ n ∗
      "Hprev" ∷ l.[dll.Node.t, "prev"] ↦ prev ∗
      "His_dlist" ∷ is_dlist_node n last l next xs
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

Lemma is_dlist_node_last_null_nil fst prev next xs :
  is_dlist_node fst null prev next xs -∗ ⌜xs = []⌝.
Proof.
  move: fst prev next.
  elim xs => [|x xs' IH] fst prev next //=.
  - by auto.
  - iIntros "(%n & H)".
    iNamed "H".
    iPoseProof (IH with "His_dlist") as "->".
    simpl.
    iDestruct "His_dlist" as "[-> ->]".
    iDestruct "Hl" as "%H".
    by done.
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

Lemma is_dlist_node_last_not_null_snoc fst last next xs :
  last ≠ null ->
  is_dlist_node fst last null next xs -∗
  ∃x xs', ⌜xs = xs' ++ [x]⌝.
Proof.
  move => H.
  iIntros "H".
  elim xs using rev_ind.
  - simpl.
    by iDestruct "H" as "[_ ->]".
  - move => x l IH.
    by iExists x, l.
Qed.

Inductive Sorted : list w64 -> Prop :=
  | Sorted_nil : Sorted []
  | Sorted_one w : Sorted [w]
  | Sorted_cons a b xs :
    Sorted (b :: xs) ->
    uint.Z a ≤ uint.Z b ->
    Sorted (a :: b :: xs).

Lemma Sorted_tail (x : w64) (xs : list w64) : Sorted (x :: xs) -> Sorted xs.
Proof.
  elim xs => [|x' [|y ys]]; [by constructor|by constructor|].
  move => IH H.
  by inv H.
Qed.

Lemma Sorted_snoc (xs : list w64) (y : w64) : Sorted xs -> (∀ x, x ∈ xs -> uint.Z x ≤ uint.Z y) -> Sorted(xs ++ [y]).
Proof.
  elim xs; [by constructor|].
  move => a l IH Hsorted Hy //=.
  move: IH Hy Hsorted.
  case l => [|b l'] IH Hy Hsorted.
  - apply Sorted_cons.
    + apply IH; first by apply Sorted_nil.
      move => x Hx.
      rewrite elem_of_nil in Hx.
      case Hx.
    + apply Hy.
      rewrite elem_of_cons.
      left.
      done.
  - simpl.
    apply Sorted_cons.
    + apply IH.
      * by apply (Sorted_tail a).
      * move => x Hx.
        apply Hy.
        by rewrite elem_of_cons; right.
    + by inv Hsorted.
Qed.

Lemma Sorted_app (xs ys : list w64) (x y : w64) :
  Sorted (xs ++ [x]) ->
  Sorted (y :: ys) ->
  uint.Z x ≤ uint.Z y ->
  Sorted (xs ++ x :: y :: ys).
Proof.
  elim xs => [|a xs'] //=.
  - move => Hxs Hys Hxy.
    by apply Sorted_cons.
  - case xs' => [|b xs''] //=.
    + move => IH Hxs Hys Hxy.
      apply Sorted_cons.
      * by apply IH; eauto using Sorted_one.
      * by inv Hxs.
    + move => IH Hxs Hys Hxy.
      inv Hxs.
      apply Sorted_cons; by eauto using IH.
Qed.

Lemma Sorted_app_left (xs ys : list w64) :
  Sorted (xs ++ ys) ->
  Sorted xs.
Proof.
  elim: xs => [|x xs Hxs] H.
  - apply Sorted_nil.
  - move: xs Hxs H => [|x' xs] Hxs H.
    + apply Sorted_one.
    + inv H.
      constructor.
      * by apply Hxs.
      * auto.
Qed.

Lemma Sorted_app_right (xs ys : list w64) :
  Sorted (xs ++ ys) ->
  Sorted ys.
Proof.
  elim: xs => [|x xs Hxs] H.
  - by done.
  - move: xs Hxs H => [|x' xs] Hxs H.
    + by eauto using Sorted_tail.
    + inv H.
      by auto.
Qed.


Lemma Sorted_insert a y (xs ys : list w64) :
  Sorted (xs ++ y :: ys) ->
  (∀ x, x ∈ xs -> uint.Z x ≤ uint.Z a) ->
  uint.Z a ≤ uint.Z y ->
  Sorted (xs ++ a :: y :: ys).
Proof.
  move => Hxsys Hxsa Hay.
  move: (Sorted_app_left _ _ Hxsys) => Hxs.
  apply Sorted_app.
  - by apply Sorted_snoc.
  - by eauto using Sorted_app_right.
  - by auto.
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
    iDestruct "HSorted" as "%HSorted".
    rewrite app_nil_r in HSorted.
    iPureIntro; split; first by auto.
    apply Sorted_snoc; first by auto.
    move => x Hx.
    by move: (Hyv x Hx).
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
              ** rewrite elem_of_cons elem_of_nil in Hy'.
                 move: Hy' => [Hy' | Hfalse]; last by done.
                 subst y.
                 lia.
        -- iFrame.
           iApply is_dlist_node_app.
           iExists p, cur.
           by iFrame.
      * iApply "HΦ".
        iExists ys, (z :: zs').
        iFrame.
        iDestruct "HSorted" as "%HSorted".
        iPureIntro; split; first by auto.
        apply Sorted_insert; [by done|by done|].
        lia.
Qed.

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
    iSplitR; [by iPureIntro; apply Sorted_one|].
    rewrite /own_list.
    iExists l', l'.
    simpl.
    iFrame.
    iPoseProof (typed_pointsto_not_null l' {| dll.Node.val' := v; dll.Node.next' := null; dll.Node.prev' := null |} with "[$Hl]") as "%Hl".
    iStructNamed "Hl".
    simpl.
    iFrame.
    by done.
  - wp_apply (t with "[$His_dlist]"); first by done.
    iIntros (prev node) "(%ys & %zs & (-> & %Hsorted') & Hdlist_hd & Hdlist_node)".
    wp_auto.
    wp_alloc new as "Hnew".
    wp_auto.
    iAssert (⌜new ≠ null⌝)%I with "[Hnew]" as "%Hnew".
    {
      by iApply typed_pointsto_not_null in "Hnew".
    }
    wp_if_join (λ x,
      ⌜x=execute_val⌝ ∗
      ∃ new_tl,
        newNode_ptr ↦ new ∗
        l_ptr ↦ l ∗
        is_dlist_node new new_tl prev null (v :: zs) ∗
        l.[dll.List.t, "tail"] ↦ new_tl
    )%I with "[newNode Hdlist_node Hnew Htail l n]".
    {
      iSplitR; first by done.
      iExists new.
      simpl.
      iFrame.
      iExists null.
      iStructNamed "Hnew".
      simpl.
      iSplitL ""; first by done.
      iFrame.
      iFrameNamed.
      iPoseProof (is_dlist_node_null_nil with "Hdlist_node") as "->".
      by simpl.
    }
    {
      iStructNamed "Hnew"; simpl.
      iPoseProof (is_dlist_node_not_null_cons with "Hdlist_node") as "(%x & %xs & ->)"; first by auto.
      simpl; iDestruct "Hdlist_node" as "(%n' & _ & H)".
      iNamed "H".
      wp_auto.
      iSplitR; first by done.
      iExists tl.
      iFrame.
      iSplitL; by done.
    }
    iIntros (v') "(-> & %new_tl & HnewNode & Hl_ptr & Hdlist_new & Htail)".
    wp_auto.
    wp_if_join (λ x,
      ⌜x=execute_val⌝ ∗
      ∃ new_hd,
        newNode_ptr ↦ new ∗
        l_ptr ↦ l ∗
        is_dlist_node new_hd new_tl null null (ys ++ v :: zs) ∗
        l.[dll.List.t, "head"] ↦ new_hd
    )%I with "[Hdlist_hd Hdlist_new HnewNode Hl_ptr p Hhead]".
    {
      simpl.
      iDestruct "Hdlist_new" as "(%n' & H)".
      iNamed "H".
      iSplitR; first by done.
      iExists new.
      iFrame.
      iApply is_dlist_node_app.
      iExists null, new.
      simpl.
      iFrame.
      iPoseProof (is_dlist_node_last_null_nil with "[Hdlist_hd]") as "->"; first by done.
      by done.
    }
    {
      iPoseProof (is_dlist_node_last_not_null_snoc with "[$Hdlist_hd]") as "(%y & %ys' & ->)"; first by auto.
      iPoseProof (is_dlist_node_app with "Hdlist_hd") as "(%mid_last & %mid_fst & Hys' & Hy)".
      simpl.
      iDestruct "Hy" as "(%n' & Hy)".
      iNamed "Hy".
      iDestruct "His_dlist" as "[-> ->]".
      iDestruct "Hdlist_new" as "(%n1 & Hnew)".
      iNamedSuffix "Hnew" "1".
      iDestruct "Hl1" as "%Hl1".
      wp_auto.
      iSplitR; first by auto.
      iExists hd.
      rewrite is_dlist_node_app.
      iSplitL "HnewNode"; first by iFrame.
      iSplitL "Hl_ptr"; first by iFrame.
      iSplitR "Hhead"; last by iFrame.
      iExists mid_fst, new.
      rewrite is_dlist_node_app.
      simpl.
      iSplitR "Hval1 Hnext1 Hprev1 His_dlist1".
      { iExists mid_last, mid_fst.
        by iFrame. }
      iExists n1.
      by iFrame.
    }
    iIntros (v') "[-> (%new_hd & HnewNode & Hl & H & Hhead)]".
    wp_auto.
    iApply "HΦ".
    iExists ys, zs.
    repeat (iSplitR; first by done).
    iFrame.
    have ->: w64_word_instance .(word.add) (W64 (length (ys ++ zs))) (W64 1) = W64 (length (ys ++ v :: zs)); last by done.
    rewrite !length_app.
    simpl.
    word.
Qed.

End proof.

