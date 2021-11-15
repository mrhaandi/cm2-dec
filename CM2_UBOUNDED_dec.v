Require Import List PeanoNat Lia Relation_Operators Operators_Properties.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import M2.CM2 M2.CM2_facts.

Section Construction.
Variable M : Cm2.

Notation multi_step := (CM2.multi_step M).
Notation bounded := (CM2.bounded M).
Notation step := (CM2.step M).
Notation reaches := (CM2.reaches M).


Definition path k x := map (fun n => multi_step n x) (seq 0 k).

Lemma path_length {k x} : length (path k x) = k.
Proof. by rewrite /path map_length seq_length. Qed.

Lemma Config_eq_dec (x y : Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma option_Config_eq_dec (x y : option Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma In_pathE K x y : In (Some y) (path K x) -> exists k, k < K /\ multi_step k x = Some y.
Proof.
  move=> /in_map_iff [k] [<-] /in_seq ?.
  exists k. split; [lia|done].
Qed.

Lemma reachesE x y : reaches x y -> clos_refl_trans Config (fun x' y' => step x' = Some y') x y.
Proof.
  move=> [k]. elim: k x.
  { move=> x [] <-. by apply: rt_refl. }
  move=> k IH x. rewrite /= option_bind_iter.
  case Hxz: (step x) => [z|]; last by rewrite iter_None.
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

Lemma path_S {k x} y : step x = Some y -> path (S k) x = (Some x) :: (path k y).
Proof.
  move=> Hxy. rewrite /path /= -seq_shift map_map.
  congr cons. apply: map_ext => - ?.
  by rewrite /= option_bind_iter Hxy.
Qed.

Lemma path_S' {k x} : path (S k) x = (path k x) ++ [multi_step k x].
Proof. by rewrite /path seq_S map_app. Qed.

Lemma multi_step_loop_mod {K x k} : multi_step (S K) x = Some x ->
  multi_step k x = multi_step (k mod (S K)) x.
Proof.
  rewrite [in multi_step k x](Nat.div_mod_eq k (S K)).
  move: (k mod (S K)) => k' Hx. elim: (k / S K).
  - congr multi_step. lia.
  - move=> n IH. have ->: S K * S n + k' = S K + (S K * n + k') by lia.
    by move: Hx => /multi_step_plus ->.
Qed.

Lemma path_loopE K x : In (multi_step K x) (path K x) -> 
  forall k, In (multi_step k x) (path K x).
Proof.
  elim: K x; first done.
  move=> K IH x. rewrite [multi_step _ _]/= option_bind_iter.
  case Hxz: (step x) => [z|].
  - move=> H. rewrite (path_S z Hxz) /= in H. case: H.
    + move=> Hzx. have /multi_step_loop_mod : multi_step (S K) x = Some x.
      { by rewrite /multi_step /= option_bind_iter Hxz. }
      move=> Hx k. rewrite Hx. apply /in_map_iff. exists (k mod (S K)).
      split; first done. apply /in_seq.
      have := Nat.mod_upper_bound k (S K). lia.
    + rewrite (path_S z Hxz).
      move=> /IH {}IH [|k]; first by left.
      rewrite /= option_bind_iter Hxz. right. by apply: IH.
  - rewrite iter_None. move=> /in_map_iff [k] [Hk] /in_seq HK.
    move=> k'. have [|Hkk'] : k' < k \/ k <= k' by lia.
    + move=> ?. apply /in_map_iff. exists k'.
      split; first done. apply /in_seq. lia.
    + move: (Hk) => /(multi_step_k_monotone k') ->; [done|right].
      suff ->: (K = S (K - 1)) by left.
      move: K HK {IH} => [|K] ?; last by lia.
      move: Hk. by have ->: k = 0 by lia.
Qed.


Lemma path_loopE' K x : In (multi_step K x) (path K x) -> 
  forall y, reaches x y -> In (Some y) (path K x).
Proof.
  move=> /path_loopE H y [k] H'. move: (H k).
  by congr In.
Qed.

Lemma path_noloopI k x :
  ~ In (multi_step k x) (path k x) -> NoDup (path (k + 1) x).
Proof.
  elim: k x.
  { move=> ??. constructor; [done| constructor]. }
  move=> k IH x.
  rewrite path_S' /multi_step in_app_iff /= -/(multi_step k x).
  move=> /Decidable.not_or.
  have [|/IH ?] := In_dec option_Config_eq_dec (multi_step k x) (path k x).
  - move=> /path_loopE /(_ (S k)). tauto.
  - move=> [?] ?.
    apply /(NoDup_Add (a := multi_step (S k) x) (l := path (k + 1) x)).
    + rewrite path_S'.
      have := Add_app (multi_step (k + 1) x) (path (k + 1) x) [].
      congr Add.
      * congr multi_step. lia.
      * by rewrite app_nil_r.
    + constructor; first done.
      have ->: k + 1 = S k by lia.
      rewrite path_S' in_app_iff /=. tauto.
Qed.


Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (multi_step K x) => [y|].
  - have [Hy|Hy] := In_dec option_Config_eq_dec (Some y) (path K x).
    + left. exists (map (fun oy => if oy is Some y then y else x) (path K x)).
      split. { by rewrite map_length path_length. }
      move=> z /path_loopE' => /(_ K).
      rewrite HK => /(_ Hy) ?.
      apply /in_map_iff. by exists (Some z).
    + right. move=> [L [? HL]].
      apply: (pigeonhole option_Config_eq_dec (path (K+1) x) (map Some L)).
      * move=> [z|] /in_map_iff [k] [Hk] /in_seq ?.
        { apply /in_map_iff. exists z. split; first done.
          apply: HL. by exists k. }
        by move: Hk HK => /(multi_step_k_monotone K) /(_ ltac:(lia)) ->.
      * rewrite map_length path_length. lia.
      * apply /path_noloopI. by rewrite HK.
  - left. exists (map (fun oy => if oy is Some y then y else x) (path K x)).
    split. { by rewrite map_length path_length. }
    move=> y [k]. have [?|?] : k < K \/ K <= k by lia.
    + move=> Hk. apply /in_map_iff. exists (Some y).
      split; first done.
      apply /in_map_iff. exists k. split; first done.
      apply /in_seq. lia. 
    + by move: HK => /(multi_step_k_monotone k) /(_ ltac:(lia)) ->.
Qed.


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
