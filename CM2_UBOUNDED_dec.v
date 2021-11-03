Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import M2.CM2 M2.CM2_facts.

Section Construction.
Variable M : Cm2.

Notation bounded := (bounded M).

Lemma fixed_decision K : 
  {forall x : Config, bounded K x} + {~ (forall x : Config, bounded K x)}.
Proof.
  have := Forall_dec (fun 'x => bounded K x) _
    (list_prod (seq 0 (length M)) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
Admitted.

Lemma uniform_decision : (uniformly_bounded M) + (not (uniformly_bounded M)).
Proof.
Admitted.

End Construction.

(* informative decision statement for uniform boundedness for Cm2 *)
Theorem decision (M: Cm2) : (uniformly_bounded M) + (not (uniformly_bounded M)).
Proof.
  exact: (uniform_decision M).
Qed.

(* boolean decision procedure for uniform boundedness for Cm2 *)
Definition decider (M: Cm2) : bool :=
  match decision M with
  | inl _ => true
  | inr _ => false
  end.

(* decision procedure correctness *)
Lemma decider_spec (M: Cm2) :
  (uniformly_bounded M) <-> (decider M = true).
Proof.
  rewrite /decider. case: (decision M); intuition done.
Qed.
