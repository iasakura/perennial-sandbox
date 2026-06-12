(* Correctness proof of the sorted doubly-linked list implemented in Go
   (dll/list.go), verified against its goose translation. The main result is
   insertSorted_spec: InsertSorted on a sorted list inserts the value while
   keeping the list sorted. *)
From New.proof Require Import proof_prelude.
From New.proof Require Import utils.
From New.code.github_com.iasakura.perennial_sandbox Require Import dll.
From New.generatedproof.github_com.iasakura.perennial_sandbox Require Import dll.
Require Import stdpp.sorting.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : dll.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".
Open Scope Z.

#[global] Instance : IsPkgInit (iProp Σ) dll := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) dll := build_get_is_pkg_init_wf.

(**
  The invariant of list nodes.
  [l] points to a dlist node and [last] is a pointer in the list.
  The elements between [l] and [last] including themselves are maintained by this invariant.
  The parameters [prev] is the value of the previous pointer of [l] and [next] is the next pointer of [last].
  They are used to show lemma like [is_dlist_node_app].
*)
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
  case/snocP: xs => [|xs' x].
  - simpl.
    by iDestruct "H" as "[_ ->]".
  - by iExists x, xs'.
Qed.

Notation W64Sorted := (StronglySorted (λ x y, uint.Z x ≤ uint.Z y)).

Section Sorted.
(* Auxiliary lemmas for W64Sorted. *)

Lemma StronglySorted_one {A : Type} (x : A) P : StronglySorted P [x].
Proof.
  repeat constructor.
Qed.

Lemma W64Sorted_snoc (xs : list w64) (y : w64) : W64Sorted xs -> (∀ x, x ∈ xs -> uint.Z x ≤ uint.Z y)%Z -> W64Sorted (xs ++ [y]).
Proof.
  move => H Hy.
  rewrite StronglySorted_app.
  split.
  + move => x1 x2.
    rewrite elem_of_cons elem_of_nil.
    move => Hx1 [-> | []].
    by auto.
  + split; first by done.
    apply StronglySorted_one.
Qed.

Lemma W64Sorted_app (xs ys : list w64) (x y : w64) :
  W64Sorted (xs ++ [x]) ->
  W64Sorted (y :: ys) ->
  (uint.Z x ≤ uint.Z y)%Z ->
  W64Sorted (xs ++ x :: y :: ys).
Proof.
  move => Hxs Hys Hxy.
  have ->: xs ++ x :: y :: ys = (xs ++ [x]) ++ y :: ys by rewrite -app_assoc.
  rewrite StronglySorted_app.
  split_and; [|done..].

  rewrite StronglySorted_app in Hxs.
  rewrite StronglySorted_cons in Hys.
  move: Hys Hxs => [Hy Hys] [Hx [Hxs _]].
  rewrite Forall_forall in Hy Hx.

  move => x1 x2.

  rewrite elem_of_app !elem_of_cons elem_of_nil.
  move => Hx1 Hx2.

  have Hx1x : uint.Z x1 ≤ uint.Z x.
  {
    move: Hx1 => [Hx1 | [-> | []]].
    - apply Hx; first by auto.
      by rewrite elem_of_cons; left.
    - lia.
  }
  have Hyx2 : uint.Z y ≤ uint.Z x2.
  {
    move: Hx2 => [-> | Hx2].
    - lia.
    - by apply Hy.
  }
  lia.
Qed.

Lemma W64Sorted_insert a y (xs ys : list w64) :
  W64Sorted (xs ++ y :: ys) ->
  (∀ x, x ∈ xs -> uint.Z x ≤ uint.Z a) ->
  uint.Z a ≤ uint.Z y ->
  W64Sorted (xs ++ a :: y :: ys).
Proof.
  move => Hxsys Hxsa Hay.
  move: (StronglySorted_app_1_l _ _ _ Hxsys) => Hxs.
  apply W64Sorted_app.
  - by apply W64Sorted_snoc.
  - by eauto using StronglySorted_app_1_r.
  - by auto.
Qed.

End Sorted.

Lemma findLeastGreaterNode_spec (l last : loc) (v : w64) (xs : list w64):
  {{{ is_pkg_init dll ∗ is_dlist_node l last null null xs ∗ ⌜W64Sorted xs⌝ }}}
    l @! (go.PointerType dll.Node) @! "findLeastGreaterNode" (# v)
  {{{ prev node, RET (#prev, #node); ∃ ys zs,
        ⌜xs = ys ++ zs ∧ W64Sorted (ys ++ v :: zs)⌝ ∗
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
    apply W64Sorted_snoc; first by auto.
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
        apply W64Sorted_insert; [by done|by done|].
        lia.
Qed.

Theorem insertSorted_spec  (l : loc) (xs : list w64) (v : w64) :
  {{{ is_pkg_init dll ∗ own_list l xs ∗ ⌜ W64Sorted xs ⌝  }}}
    l @! (go.PointerType dll.List) @! "InsertSorted" #v
  {{{ RET #(); ∃ ys zs, ⌜xs = ys ++ zs ⌝ ∗ ⌜W64Sorted (ys ++ v :: zs)⌝ ∗ own_list l (ys ++ v :: zs)}}}.
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
    iSplitR; [by iPureIntro; apply StronglySorted_one|].
    rewrite /own_list.
    iExists l', l'.
    simpl.
    iFrame.
    iPoseProof (typed_pointsto_not_null l' {| dll.Node.val' := v; dll.Node.next' := null; dll.Node.prev' := null |} with "[$Hl]") as "%Hl".
    iStructNamed "Hl".
    simpl.
    iFrame.
    by done.
  - wp_apply (findLeastGreaterNode_spec with "[$His_dlist]"); first by done.
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

