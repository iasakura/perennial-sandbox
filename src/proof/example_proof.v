(* Hand-written proofs about the example package.
   Demonstrates the Perennial `New` proof workflow on goose-translated Go. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.perennial_sandbox Require Import example.
From New.generatedproof.github_com.iasakura.perennial_sandbox Require Import example.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : example.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) example := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) example := build_get_is_pkg_init_wf.

(* Add returns the (wrapping) machine-word sum of its arguments. *)
Lemma wp_Add (a b : w64) :
  {{{ is_pkg_init example }}}
    @! example.Add #a #b
  {{{ RET #(word.add a b); True }}}.
Proof.
  wp_start.
  wp_auto.
  by iApply "HΦ".
Qed.

(* SumTo computes 0 + 1 + ... + (n-1).
   We specify the result as the Gauss sum over Z, assuming no overflow so the
   machine-word accumulator faithfully tracks the mathematical sum. *)
Lemma wp_SumTo (n : w64) :
  {{{ is_pkg_init example ∗ ⌜(uint.Z n * uint.Z n < 2 ^ 64)%Z⌝ }}}
    @! example.SumTo #n
  {{{ (r : w64), RET #r; ⌜(uint.Z r = uint.Z n * (uint.Z n - 1) / 2)%Z⌝ }}}.
Proof.
  wp_start as "%Hno_overflow".
  wp_auto.
  (* Loop invariant. The accumulator equation is stated multiplicatively
     (2*total = i*(i-1)) to avoid integer division inside the invariant, which
     makes the word/lia automation tractable. We also carry that total itself
     stays in range. *)
  iAssert (∃ (i total : w64),
    "i" ∷ i_ptr ↦ i ∗
    "total" ∷ total_ptr ↦ total ∗
    "%Hle" ∷ ⌜(uint.Z i ≤ uint.Z n)%Z⌝ ∗
    "%Hsum" ∷ ⌜(2 * uint.Z total = uint.Z i * (uint.Z i - 1))%Z⌝
  )%I with "[$i $total]" as "IH".
  { iPureIntro. split; word. }
  wp_for "IH".
  wp_if_destruct.
  - (* loop body: i < n. Update is total += i; i += 1. *)
    wp_for_post.
    (* Range facts for the overflow side-conditions. *)
    pose proof (word.unsigned_range n) as Hn.
    pose proof (word.unsigned_range i) as Hi.
    pose proof (word.unsigned_range total) as Ht.
    (* No overflow: total + i ≤ n(n-1)/2 < 2^64, and i + 1 ≤ n. *)
    assert (uint.Z total + uint.Z i < 2 ^ 64)%Z as Hno1 by nia.
    assert (uint.Z i + 1 < 2 ^ 64)%Z as Hno2 by nia.
    iFrame. iPureIntro. split.
    + word.
    + (* 2*(total+i) = (i+1)*i,  using 2*total = i*(i-1) *)
      rewrite !word.unsigned_add_nowrap //.
      replace (uint.Z (W64 1)) with 1%Z by word. nia.
  - (* loop exit: i = n. total is the answer; divide the invariant by 2. *)
    iApply "HΦ". iPureIntro.
    (* i = n from Hle and ¬(i<n). *)
    assert (uint.Z i = uint.Z n) as Hi_eq by lia.
    rewrite -Hi_eq.
    (* Goal: total = (i*(i-1))/2. Rewrite numerator using Hsum, then /2. *)
    rewrite -Hsum.
    rewrite Z.mul_comm Z.div_mul //.
Qed.

End proof.
