Require Import List ListDec Lia PeanoNat Relation_Operators.
Import ListNotations.

Require Import M2.Facts M2.CM2.

Require Import ssreflect ssrbool ssrfun.

Lemma Config_eta (x : Config) : x = (state x, (value1 x, value2 x)).
Proof. by move: x => [? [? ?]]. Qed.

Lemma Config_eq_dec (x y : Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma option_Config_eq_dec (x y : option Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Definition reaches_plus (M: Cm2) (x y: Config) := exists k, 0 < k /\ steps M k x = Some y.
Definition non_terminating (M: Cm2) (x: Config) := forall k, steps M k x <> None.

Section Facts.
Context {M : Cm2}.

Notation step := (CM2.step M).
Notation steps := (CM2.steps M).
Notation reaches := (CM2.reaches M).
Notation reaches_plus := (reaches_plus M).
Notation terminating := (CM2.terminating M).
Notation non_terminating := (non_terminating M).

Lemma steps_k_monotone {k x} k' : steps k x = None -> k <= k' -> steps k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
Qed.

Lemma reaches_refl x : reaches x x.
Proof. by exists 0. Qed.

Lemma step_reaches {x y} : step x = Some y -> reaches x y.
Proof. move=> ?. by exists 1. Qed.

Lemma step_reaches_plus {x y} : step x = Some y -> reaches_plus x y.
Proof. move=> ?. exists 1. split; [lia|done]. Qed.

Lemma steps_plus {k x k' y} :
  steps k x = Some y -> steps (k + k') x = steps k' y.
Proof. rewrite /steps iter_plus. by move=> ->. Qed.

Lemma steps_sub {i j x y z} :
  i <= j ->
  steps i x = Some y ->
  steps j x = Some z ->
  steps (j-i) y = Some z.
Proof.
  move=> ? Hi. rewrite [in steps j x](ltac:(lia) : j = i + (j - i)).
  by rewrite /steps iter_plus -/(steps _ _) Hi.
Qed.

Lemma step_None x : step x = None <-> nth_error M (state x) = None.
Proof.
  rewrite /step. case: (nth_error M (state x)) => [i|]; last done.
  case: i; first done.
  by move: (value1 x) (value2 x) => [|?] [|?] [].
Qed.

Lemma reaches_plus_reaches {x y z} : reaches_plus x y -> reaches y z -> reaches_plus x z.
Proof.
  move=> [k [? Hk]] [k' Hk']. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_reaches_plus {x y z} : reaches x y -> reaches_plus y z -> reaches_plus x z.
Proof.
  move=> [k Hk] [k' [? Hk']]. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_plus_incl {x y} : reaches_plus x y -> reaches x y.
Proof. move=> [k [? Hk]]. by exists k. Qed.

Lemma reaches_neq_incl {x y} : reaches x y -> x <> y -> reaches_plus x y.
Proof.
  move=> [[|k]]; first by move=> [->].
  move=> ? _. exists (S k). split; [lia|done].
Qed.

Lemma reaches_terminating {x y} : reaches x y -> terminating y -> terminating x.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k').
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma reaches_non_terminating {x y} : reaches x y -> non_terminating y -> non_terminating x.
Proof.
  move=> [k Hk] Hy k'.
  have [|->] : k' <= k \/ k' = k + (k' - k) by lia.
  - by move: Hk => + /steps_k_monotone H /H => ->.
  - rewrite (steps_plus Hk). by apply: Hy.
Qed.

Lemma reaches_non_terminating' {x y} : reaches x y -> non_terminating x -> non_terminating y.
Proof.
  move=> [k' Hk'] Hx k Hk.
  apply: (Hx (k' + k)).
  by rewrite (steps_plus Hk').
Qed.

Lemma reaches_plus_state_bound {x y} : reaches_plus x y -> state x < length M.
Proof.
  move=> [k [? Hk]].
  suff: not (length M <= state x) by lia.
  move=> /nth_error_None Hx.
  move: Hk. have ->: k = S (k - 1) by lia.
  by rewrite /= obind_oiter /step Hx oiter_None.
Qed.

Lemma reaches_plus_trans {x y z} : reaches_plus x y -> reaches_plus y z -> reaches_plus x z.
Proof. by move=> /reaches_plus_incl /reaches_reaches_plus H /H. Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. move=> [k Hk] [k' Hk']. exists (k+k'). by rewrite (steps_plus Hk). Qed.

(* TODO above using relations *)
Lemma reachesE x y : reaches x y -> clos_refl_trans Config (fun x' y' => step x' = Some y') x y.
Proof.
  move=> [k]. elim: k x.
  { move=> x [] <-. by apply: rt_refl. }
  move=> k IH x. rewrite /= obind_oiter.
  case Hxz: (step x) => [z|]; last by rewrite oiter_None.
  move=> /IH ?. apply: rt_trans; last by eassumption.
  by apply: rt_step.
Qed.

Lemma reachesI x y : clos_refl_trans Config (fun x' y' => step x' = Some y') x y -> reaches x y.
Proof.
  elim.
  - move=> ???. by exists 1.
  - move=> ?. by exists 0.
  - move=> ??? _ ? _ ?. apply: reaches_trans; by eassumption.
Qed.

Lemma reaches_plus_invariant_loop (P : Config -> Prop) :
  (forall x, P x -> exists y, reaches_plus x y /\ P y) ->
  forall x, P x -> non_terminating x.
Proof.
  move=> H x Hx k. elim: k x Hx; first done.
  move=> k IH x /H [y] [[k' [? Hk']]] /IH Hk.
  move=> /(steps_k_monotone (k' + k)) /(_ ltac:(lia)).
  by rewrite (steps_plus Hk').
Qed.

Corollary reaches_plus_self_loop x : reaches_plus x x -> non_terminating x.
Proof.
  move=> ?. apply: (reaches_plus_invariant_loop (fun y => y = x)); last done.
  move=> y ->. by exists x. 
Qed.

Lemma steps_loop_mod {K x k} : steps (S K) x = Some x ->
  steps k x = steps (k mod (S K)) x.
Proof.
  rewrite [in steps k x](Nat.div_mod_eq k (S K)).
  move: (k mod (S K)) => k' Hx. elim: (k / S K).
  - congr steps. lia.
  - move=> n IH. have ->: S K * S n + k' = S K + (S K * n + k') by lia.
    by move: Hx => /steps_plus ->.
Qed.

Lemma steps_values_bound k x y : steps k x = Some y ->
  value1 x <= k + value1 y /\ value1 y <= k + value1 x /\
  value2 x <= k + value2 y /\ value2 y <= k + value2 x.
Proof.
  elim: k x. { move=> ? [<-]. lia. }
  move=> k IH x. rewrite /= obind_oiter /step -/step.
  case: (nth_error M (state x)); last by rewrite oiter_None.
  case.
  - move=> [] /IH /=; lia.
  - move=> [] ?.
    + case Hx: (value2 x) => [|?] /IH /=; lia.
    + case Hx: (value1 x) => [|?] /IH /=; lia.
Qed.

End Facts.
