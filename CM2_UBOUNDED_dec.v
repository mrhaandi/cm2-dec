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

Lemma In_pathI k x K : k < K -> In (multi_step k x) (path K x).
Proof.
  move=> ?. apply /in_map_iff. exists k. split; first done.
  apply /in_seq. lia.
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

Lemma path_S_last {k x} : path (S k) x = (path k x) ++ [multi_step k x].
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
    + move=> Hzx k. have /multi_step_loop_mod -> : multi_step (S K) x = Some x.
      { by rewrite /multi_step /= option_bind_iter Hxz. }
      by apply /In_pathI /(Nat.mod_upper_bound k (S K)).
    + rewrite (path_S z Hxz).
      move=> /IH {}IH [|k]; first by left.
      rewrite /= option_bind_iter Hxz. right. by apply: IH.
  - rewrite iter_None. move=> /in_map_iff [k] [Hk] /in_seq HK.
    move=> k'. have [|Hkk'] : k' < k \/ k <= k' by lia.
    + move=> ?. apply: In_pathI. lia.
    + move: (Hk) => /(multi_step_k_monotone k') /(_ Hkk') ->.
      rewrite -Hk. apply: In_pathI. lia.
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
  rewrite path_S_last /multi_step in_app_iff /= -/(multi_step k x).
  move=> /Decidable.not_or.
  have [|/IH ?] := In_dec option_Config_eq_dec (multi_step k x) (path k x).
  - move=> /path_loopE /(_ (S k)). tauto.
  - move=> [?] ?.
    apply /(NoDup_Add (a := multi_step (S k) x) (l := path (k + 1) x)).
    + rewrite path_S_last.
      have := Add_app (multi_step (k + 1) x) (path (k + 1) x) [].
      congr Add.
      * congr multi_step. lia.
      * by rewrite app_nil_r.
    + constructor; first done.
      have ->: k + 1 = S k by lia.
      rewrite path_S_last in_app_iff /=. tauto.
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
      rewrite -Hk. by apply: In_pathI.
    + by move: HK => /(multi_step_k_monotone k) /(_ ltac:(lia)) ->.
Qed.

(* one way
bounded K x -> multi_step K x = Some y -> exists k', k' < K /\ multi_step k' x = Some y.

K <= a -> bounded K (p, (K, b)) -> bounded K (p, (a, b))
*)

Lemma multi_step_values_bound k x y : multi_step k x = Some y ->
  value1 x <= k + value1 y /\ value1 y <= k + value1 x /\
  value2 x <= k + value2 y /\ value2 y <= k + value2 x.
Proof.
  elim: k x. { move=> ? [<-]. lia. }
  move=> k IH x. rewrite /= option_bind_iter /step -/step.
  case: (nth_error M (state x)); last by rewrite iter_None.
  case.
  - move=> [] /IH /=; lia.
  - move=> [] ?.
    + case Hx: (value2 x) => [|?] /IH /=; lia.
    + case Hx: (value1 x) => [|?] /IH /=; lia.
Qed.

Lemma nth_error_seq {i start len} :
  i < len -> nth_error (seq start len) i = Some (start + i).
Proof.
  elim: len i start; first by lia.
  move=> len IH [|i] start.
  { move=> ?. congr Some. lia. }
  move=> ?. rewrite /= IH; first by lia.
  congr Some. lia.
Qed.

Lemma shift_multi_step_a k K p a b :
  k <= K ->
  multi_step k (p, (K + a, b)) =
  match multi_step k (p, (K, b)) with
  | Some (p', (a', b')) => Some (p', (a' + a, b'))
  | None => None
  end.
Proof.
  elim: k K p a b; first done.
  move=> k IH [|K] p a b ?; first by lia.
  rewrite /multi_step /= ?option_bind_iter /step -/step /=.
  case: (nth_error M p); last by rewrite ?iter_None.
  case.
  - move=> c. rewrite -IH; first by lia.
    congr multi_step. congr (_, (_, _)). lia.
  - move=> [] q.
    + case: b => [|b]; rewrite -IH; by [|lia].
    + rewrite -IH; by [|lia].
Qed.

Lemma shift_multi_step_b k K p a b :
  k <= K ->
  multi_step k (p, (a, K + b)) =
  match multi_step k (p, (a, K)) with
  | Some (p', (a', b')) => Some (p', (a', b' + b))
  | None => None
  end.
Proof.
  elim: k K p a b; first done.
  move=> k IH [|K] p a b ?; first by lia.
  rewrite /multi_step /= ?option_bind_iter /step -/step /=.
  case: (nth_error M p); last by rewrite ?iter_None.
  case.
  - move=> c. rewrite -IH; first by lia.
    congr multi_step. congr (_, (_, _)). lia.
  - move=> [] q.
    + rewrite -IH; by [|lia].
    + case: a => [|a]; rewrite -IH; by [|lia].
Qed.

Lemma shift_path_a K p a b :
  path (K+1) (p, (K+a, b)) =
  map (fun oy => if oy is Some (p', (a', b')) then Some (p', (a'+a, b')) else None) (path (K+1) (p, (K, b))).
Proof. 
  rewrite /path map_map. apply: map_ext_in => k /in_seq ?.
  apply: shift_multi_step_a. lia.
Qed.

Lemma shift_path_b K p a b :
  path (K+1) (p, (a, K+b)) =
  map (fun oy => if oy is Some (p', (a', b')) then Some (p', (a', b'+b)) else None) (path (K+1) (p, (a, K))).
Proof. 
  rewrite /path map_map. apply: map_ext_in => k /in_seq ?.
  apply: shift_multi_step_b. lia.
Qed.

Lemma path_NoDup_a_bound K p a b : K <= a -> NoDup (path (K+1) (p, (a, b))) -> NoDup (path (K+1) (p, (K, b))).
Proof.
  move=> ?. have ->: a = K+(a-K) by lia.
  rewrite shift_path_a. by apply: NoDup_map_inv.
Qed.

Lemma path_NoDup_b_bound K p a b : K <= b -> NoDup (path (K+1) (p, (a, b))) -> NoDup (path (K+1) (p, (a, K))).
Proof.
  move=> ?. have ->: b = K+(b-K) by lia.
  rewrite shift_path_b. by apply: NoDup_map_inv.
Qed.


Lemma fixed_decision K :
  {forall x : Config, bounded K x} + {~ (forall x : Config, bounded K x)}.
Proof.
  (* need to check configurations up to values K *)
  have := Forall_dec (fun 'x => bounded K x) (pointwise_decision K)
    (list_prod (seq 0 (length M)) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
  case; first last.
  { move=> H. right => HK. apply /H /Forall_forall. move=> ??. by apply: HK. }
  wlog: K /(0 < K).
  { move: K => [|K] H HK.
    - right. move=> /(_ (0, (0, 0))) [[|? L] [/= ? /(_ (0, (0, 0))) HL]].
      + apply: HL. by exists 0.
      + lia.
    - apply: H; [lia|done]. }
  move=> ? HK. left => x.
  have [/path_loopE'|/path_noloopI] := In_dec option_Config_eq_dec (multi_step K x) (path K x).
  { (* bounded by path *)
    move=> H. exists (map (fun oy => if oy is Some y then y else x) (path K x)).
    split. { by rewrite map_length path_length. }
    move=> y /H ?. apply /in_map_iff. by exists (Some y). }
  case Hz: (multi_step K x) => [z|]; first last.
  { (* bounded by terminating path *)
    move=> _. exists (map (fun oy => if oy is Some y then y else x) (path K x)).
    split. { by rewrite map_length path_length. }
    move=> y [k Hk]. have : not (K <= k).
    { move=> ?. by move: Hz Hk => /(multi_step_k_monotone k) ->. }
    move=> ?. apply /in_map_iff. exists (Some y). split; first done.
    rewrite -Hk. apply: In_pathI. lia. }
  (* not bounded *)
  move=> Hx. exfalso.
  move: x Hx Hz => [p [a b]] Hx Hz.
  have Hp : not (length M <= p).
  { move=> /nth_error_None HM. move: Hz. have -> : K = S (K - 1) by lia.
    by rewrite /multi_step /= option_bind_iter /step /= HM iter_None. }
  move: Hx Hz.
  (* it suffices to consider configurations up to values K  *)
  wlog: a b z /(a <= K /\ b <= K); first last.
  { move=> ? Hx Hz. suff: bounded K (p, (a, b)).
    { move=> [L [? HL]]. 
      apply: (pigeonhole option_Config_eq_dec _ (map Some L) _ _ Hx).
      - move=> [{}y|].
        + move=> /In_pathE [k [? Hk]]. apply /in_map_iff.
          exists y. split; first done.
          apply: HL. by exists k.
        + move=> /in_map_iff [k'] [+ /in_seq ?].
          move=> /(multi_step_k_monotone K) /(_ ltac:(lia)).
          by rewrite Hz.
      - rewrite map_length path_length. lia. }
    move: HK => /Forall_forall.
    apply. apply: in_prod; [|apply: in_prod]; apply /in_seq; lia. }
  move=> H'K.
  wlog: a b z /(a <= K).
  { move=> H. have [/H|->] : a <= K \/ a = K + (a - K) by lia.
    { by apply. }
    move=> /path_NoDup_a_bound => /(_ ltac:(lia)) /H {H}.
    rewrite shift_multi_step_a; first done.
    case: (multi_step K (p, (K, b))) => [y|]; last done.
    move=> H _. by apply: (H y). }
  move=> ?. have [?|->] : b <= K \/ b = K + (b - K) by lia.
  { move=> /H'K H /H. by apply. }
  move=> /path_NoDup_b_bound => /(_ ltac:(lia)) /H'K.
  rewrite shift_multi_step_b; first done.
  case: (multi_step K (p, (a, K))) => [y|]; last done.
  move=> H _. by apply: (H y).
Qed.

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
