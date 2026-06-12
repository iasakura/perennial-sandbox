(* General-purpose helpers shared by the proofs in this repo. *)
From stdpp Require Import prelude.

(* Spec view for case analysis on a list from the rear: [case/snocP: xs => [|xs' x]]. *)
Variant snoc_spec {A} : list A → Prop :=
  | SnocNil : snoc_spec []
  | SnocApp (l : list A) (x : A) : snoc_spec (l ++ [x]).

Lemma snocP {A} (l : list A) : snoc_spec l.
Proof. induction l using rev_ind; constructor. Qed.
