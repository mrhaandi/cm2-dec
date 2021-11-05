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

Definition path k x := map (fun n => if multi_step n x is Some y then y else x) (seq 0 k).

Lemma path_length {k x} : length (path k x) = k.
Proof. by rewrite /path map_length seq_length. Qed.

Lemma Config_eq_dec (x y : Config) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma In_pathE K x y : In y (path K x) -> x = y \/ exists k, 0 < k < K /\ multi_step k x = Some y.
Proof.
  move=> /in_map_iff [[|k]].
  { move=> [<-] _. by left. }
  case Hk: (multi_step (S k) x) => [z|].
  - move=> [<-] /in_seq ?. right. exists (S k).
    split; [lia|done].
  - move=> [? _]. by left.
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

Lemma let_try2 K x y : multi_step K x = Some y ->
  In y (path K x) -> forall z, reaches x z -> In z (path K x).
Proof.
  elim: K y; first done.
  move=> K IH y. rewrite [multi_step _ _]/=.
  case Hxz: (multi_step K x) => [z|]; last done.
  move=> Hzy. have -> : S K = K + 1 by lia.
  rewrite /path seq_app map_app -/(path _ _) /= Hxz.
  move=> /in_app_iff [|].
  - move=> /IH.  Hxz => /IH {}IH. 
  move=> Hy. move: (Hy) => /IH {}IH. rewrite [In y _]/= => - [|].
  { move=> ? z'. subst y.    } 
  { done. }

Lemma let_try2_dups K x y : multi_step K x = Some y ->
  In y (path K x) -> forall z, reaches x z -> In z (path K x).
Proof.
  move=> HK Hy.
  have /(pigeonhole Config_eq_dec) : incl (path (K+1) x) (path K x).
  { move=> z. rewrite /path seq_app map_app.
    move=> /in_app_iff [|]; first done.
    rewrite /= HK. by move=> [<-|]. }
  rewrite ?path_length => /(_ ltac:(lia)).
  move=> /(dup_seq Config_eq_dec).
  
  Search (In _ (_ ++ _)). Search (seq _ (_ + _)).  }
  elim: K x; first done.
  move=> K IH x. rewrite [multi_step _ _]/= option_bind_iter.
  case Hxz: (step x) => [z|]; last by rewrite iter_None.
  move=> Hy. move: (Hy) => /IH {}IH. rewrite [In y _]/= => - [|].
  { move=> ? z'. subst y.    } 
  { done. }

Lemma let_try K x y : multi_step K x = Some y ->
(In y (path K x) <-> bounded K x).
Proof.
  elim: K x.
  { move=> x /= _. split; first done.
    move=> [[|? L]] /= []; last by lia.
    move=> _ /(_ x). apply. by apply: reaches_refl. }
  move=> K IH x. rewrite [multi_step _ _]/= option_bind_iter.
  case Hxz: (step M x) => [z|]; last by rewrite iter_None.
  rewrite -/(multi_step _ _) => HK.
  move: (HK) => /IH {}IH. split.
  - move=> /In_pathE [].
    + move=> ?. subst y. exists (path (K+1) x).
      rewrite path_length. split; first by lia.
      move=> y' /reachesE /(clos_rt_rt1n Config) []. admit.
      
      admit. 
    admit.
    + move=> [k [? Hk]].
      have /IH : In y (path K z).
      { apply /in_map_iff. exists (k-1). }
      move=> [L] [? HL]. exists (x::L) => /=.
      split; first by lia.
      move=> y' [[|k']]. { move=> [?]. by left. }
      rewrite /= option_bind_iter Hxz => ?.
      right. apply: HL. by exists k'.
  - 
Admitted.

Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (multi_step K x) => [y|].
  - have [Hy|Hy] := In_dec Config_eq_dec y (path K x).
    + left. exists (path K x). rewrite path_length.
      split; first done.
      move: (Hy) => /in_map_iff [k].
      case Hk: (multi_step k x) => [z|]; first last.
      { move=> [_] /in_seq ?.
        by move: Hk HK => /(multi_step_k_monotone K) /(_ ltac:(lia)) ->. }
      move=> [?] /in_seq ?. subst z.
      move=> z [k'].
      have [?|?] : k' < K \/ K <= k' by lia.
      { move=> Hk'. apply /in_map_iff. exists k'.
        rewrite Hk'. split; first done. apply /in_seq. lia. }
      have -> : k' = k + (k'-k) by lia.
      rewrite (Nat.div_mod_eq (k'-k) (K-k)).
      rewrite (multi_step_plus Hk).
      have := Nat.mod_upper_bound (k' - k) (K - k) ltac:(lia).
      move: (_ / _) (_ mod _) => n k'' ?.
      have : multi_step ((K - k) * n) y = Some y.
      { rewrite (ltac:(lia) : K = k + (K - k)) (multi_step_plus Hk) in HK.
        move: (K - k) HK => m Hm. elim: n; first by rewrite Nat.mul_0_r.
        move=> n IH. by rewrite Nat.mul_succ_r Nat.add_comm (multi_step_plus Hm). }
      move=> /multi_step_plus -> Hk''. apply /in_map_iff. exists (k+k'').
      rewrite (multi_step_plus Hk) Hk''. split; first done.
      apply /in_seq. lia.
    + right. move=> [L [? HL]].
      apply: (pigeonhole Config_eq_dec (path (K+1) x) L).
      * move=> z /in_map_iff [k] [<-] _. apply: HL.
        case Hk: (multi_step k x) => [{}z|]; [by exists k | by exists 0].
      * rewrite path_length. lia.
      * case: (NoDup_dec Config_eq_dec (path (K + 1) x)); first done.
        move=> /(dup_seq Config_eq_dec) [[i j]].
        admit.
  - left. exists (path K x). rewrite length_path. split; first done.
    move=> y [k]. have [?|?] : k < K \/ K <= k by lia.
    + move=> Hk. apply /in_map_iff. exists k. rewrite Hk in_seq.
      split; [done|lia].
    + by move: HK => /(multi_step_k_monotone k) /(_ ltac:(lia)) ->.
Admitted.


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
