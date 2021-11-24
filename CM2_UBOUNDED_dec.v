Require Import List ListDec PeanoNat Lia Relation_Operators Operators_Properties.
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

Lemma prod_nat_nat_eq_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma In_pathE K x oy : In oy (path K x) -> exists k, k < K /\ multi_step k x = oy.
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

Lemma path_plus {k k' x} y : multi_step k x = Some y ->
  path (k+k') x = path k x ++ path k' y.
Proof.
  move=> Hxy. rewrite /path seq_app map_app /=.
  congr app.
  have ->: seq k k' = map (fun i => k+i) (seq 0 k').
  { elim: k'; first done.
    move=> k' IH. have ->: S k' = k' + 1 by lia.
    by rewrite ?seq_app IH map_app. }
  rewrite map_map. apply: map_ext => - ?.
  by move: Hxy => /multi_step_plus ->.
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

Lemma loop_bounded K x : In (multi_step K x) (path K x) -> bounded K x.
Proof.
  move=> /path_loopE' H. 
  exists (map (fun oy => if oy is Some y then y else x) (path K x)).
  split. { by rewrite map_length path_length. }
  move=> y /H {}H. apply /in_map_iff. by exists (Some y).
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

Lemma mortal_bounded {K x} : multi_step K x = None -> bounded K x.
Proof.
  move=> HK.
  exists (map (fun oy => if oy is Some y then y else x) (path K x)).
  split. { by rewrite map_length path_length. }
  move=> y [k]. have [?|?] : k < K \/ K <= k by lia.
  - move=> Hk. apply /in_map_iff. exists (Some y).
    split; first done.
    rewrite -Hk. by apply: In_pathI.
  - by move: HK => /(multi_step_k_monotone k) /(_ ltac:(lia)) ->.
Qed.

Lemma In_None_pathE k x :
  In None (path k x) -> multi_step k x = None.
Proof.
  move=> /In_pathE [k' [?]] /(multi_step_k_monotone k). apply. lia.
Qed.

Lemma NoDup_not_bounded {K x y} : 
  multi_step K x = Some y -> NoDup (path (K + 1) x) -> not (bounded K x).
Proof.
  move=> Hxy HK [L [? HL]].
  apply: (pigeonhole option_Config_eq_dec (path (K+1) x) (map Some L)).
  - move=> [z|] /in_map_iff [k] [Hk] /in_seq ?.
    { apply /in_map_iff. exists z. split; first done.
      apply: HL. by exists k. }
    by move: Hk Hxy => /(multi_step_k_monotone K) /(_ ltac:(lia)) ->.
  - rewrite map_length path_length. lia.
  - done.
Qed.

Lemma boundedE {K x} : bounded K x ->
  (In (multi_step K x) (path K x)) + (multi_step K x = None).
Proof.
  move=> HK.
  case Hy: (multi_step K x) => [y|]; last by right.
  have [?|] := In_dec option_Config_eq_dec (Some y) (path K x).
  { by left. }
  rewrite -Hy. move=> /path_noloopI /NoDup_not_bounded.
  by move=> /(_ y Hy HK).
Qed.

Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (multi_step K x) => [y|].
  - have [Hy|Hy] := In_dec option_Config_eq_dec (Some y) (path K x).
    + left. apply: loop_bounded. by rewrite HK.
    + right. apply: (NoDup_not_bounded HK).
      apply: path_noloopI. by rewrite HK.
  - left. by apply: mortal_bounded.
Qed.

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
  have [|/path_noloopI] := In_dec option_Config_eq_dec (multi_step K x) (path K x).
  { by apply: loop_bounded. }
  case Hz: (multi_step K x) => [z|]; first last.
  { move=> _. by apply: mortal_bounded. }
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
    { by apply: (NoDup_not_bounded Hz). }
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

Lemma bounded_monotone {k k' x} : k <= k' -> bounded k x -> bounded k' x.
Proof. move=> ? [L [? ?]]. exists L. split; [lia|done]. Qed.

Notation l := (length M).

(* from an arbitrary config arrive at config with at least one large value *)
Lemma uniform_decision_aux1 x : let n := l*(l+1) in
  (bounded (l*n*n+1) x) +
  { y | (exists k, k <= l*n*n /\ multi_step k x = Some y) /\ (n <= value1 y \/ n <= value2 y) }.
Proof.
  move=> n.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (multi_step (l*n*n) x) (path (l*n*n) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (multi_step (l*n*n+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right.
  have [/(pigeonhole option_Config_eq_dec)|] := incl_dec option_Config_eq_dec (path (l*n*n+1) x)
    (map Some (list_prod (seq 0 l) (list_prod (seq 0 n) (seq 0 n)))).
  { move=> H. exfalso. apply: (H _ Hx).
    rewrite path_length map_length ?prod_length ?seq_length. lia. }
  move=> /(not_inclE option_Config_eq_dec) [[z|]].
  - move=> H. exists z.
    move: H => [/in_map_iff] [k] [Hk] /in_seq ? H.
    have H'z : not (l <= state z).
    { move=> /nth_error_None Hz.
      have : multi_step (S k) x = None by rewrite /= Hk /= /step Hz.
      move=> /(multi_step_k_monotone (l*n*n+1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    split. { exists k. split; [lia|done]. }
    suff : not (value1 z < n /\ value2 z < n) by lia.
    move=> H'. apply: H. apply /in_map_iff. exists z. split; first done.
    move: z {Hk} H'z H' => [? [? ?]] /= ??.
    apply /in_prod; [|apply /in_prod]; apply /in_seq; lia.
  - move=> [/in_map_iff] H. exfalso.
    move: H => [k] [+ /in_seq ?].
    move=> /(multi_step_k_monotone (l*n*n+1)) /(_ ltac:(lia)).
    by rewrite Hxy.
Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.


Lemma Exists_sig {X : Type} P (HP : (forall x, {P x} + {~ P x})) (L : list X) :
  Exists P L -> { x | In x L /\ P x}.
Proof.
  elim: L. { by move=> /Exists_nil. }
  move=> x L IH /Exists_cons H.
  have [/IH|?] := Exists_dec P L HP.
  - move=> [y [? ?]]. exists y. by split; [right|].
  - exists x. by split; [left|tauto].
Qed.

Lemma shift_multi_step_k_b k p a b n : 
  multi_step k (p, (a, k)) = Some (p, (a, b)) ->
  forall i, i <= n -> multi_step (i*k) (p, (a, n*k)) = Some (p, (a, i*b + (n-i)*k)).
Proof.
  move=> Hk i.
  have [b' [-> ->]] : exists b', n * k = n * k + b' /\ (n - i) * k = (n - i) * k + b'.
  { exists 0. lia. }
  elim: i n b'. { move=> ???. congr (Some (_, (_, _))). lia. }
  move=> i IH [|n] b' ?; first by lia.
  rewrite /= /multi_step iter_plus -/(multi_step _ _).
  rewrite -?Nat.add_assoc.
  rewrite shift_multi_step_b; first by lia.
  rewrite Hk. have := IH n (b+b') ltac:(lia).
  congr eq.
  - congr multi_step. congr (_, (_, _)). lia.
  - congr (Some (_, (_, _))). lia.
Qed.

Lemma k_step_iter k p a1 b1 a2 b2 :
  (k <= a1 \/ a1 = a2) -> (k <= b1 \/ b1 = b2) -> 
  multi_step k (p, (a1, b1)) = Some (p, (a2, b2)) ->
  let ca := if Nat.eq_dec a1 a2 then 0 else 1 in
  let cb := if Nat.eq_dec b1 b2 then 0 else 1 in
  forall i n a b, i <= n ->
    multi_step (i*k) (p, (a1+ca*(a+n*a1),b1+cb*(b+n*b1))) =
      Some (p, (a1+ca*(a+(n-i)*a1+i*a2),b1+cb*(b+(n-i)*b1+i*b2))).
Proof.
  move=> Ha Hb Hk ca cb. elim.
  { move=> ????. congr (Some (_, (_, _))); lia. }
  move=> i IH [|n] a b; first by lia.
  move=> /(iffRL (Nat.succ_le_mono _ _)) /IH {}IH.
  rewrite /= /multi_step iter_plus -/(multi_step _ _).
  have := IH (a2+a) (b2+b). congr eq; first last.
  { congr (Some (_, (_, _))); lia. }
  congr Nat.iter.
  rewrite /ca /cb.
  move: (Nat.eq_dec a1 a2) (Nat.eq_dec b1 b2) => [?|?] [?|?] /=.
  - rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_multi_step_b; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_multi_step_a; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
  - rewrite shift_multi_step_a; first lia.
    rewrite shift_multi_step_b; first lia.
    rewrite ?Nat.add_0_r Hk.
    congr (Some (_, (_, _))); lia.
Qed.

(* probably too much? *)
Lemma not_uniformly_boundedI k p a1 b1 a2 b2 :
  (k <= a1 \/ a1 = a2) -> (k <= b1 \/ b1 = b2) -> 
  (a1 <> a2 \/ b1 <> b2) ->
  multi_step k (p, (a1, b1)) = Some (p, (a2, b2)) ->
  not (uniformly_bounded M).
Proof.
  move=> /k_step_iter H /H {}H Hab /H /= + [K].
  move=> /(_ _ K 0 0) /=.
  move Ha: (a1 + _ * _) => a.
  move Hb: (b1 + _ * _) => b.
  move=> {}H /(_ (p, (a, b))) [L [? HL]].
  have : incl (map (fun i => multi_step (i * k) (p, (a, b))) (seq 0 (K+1))) (map Some L).
  { move=> z /in_map_iff [i] [<- /in_seq ?]. rewrite H; first by lia.
    apply: in_map. apply: HL. exists (i*k). rewrite H; [lia|done]. }
  move=> /(pigeonhole option_Config_eq_dec). apply.
  { rewrite ?map_length seq_length. lia. }
  under map_ext_in.
  { move=> i /in_seq ?. rewrite H; first by lia. over. }
  apply: NoDup_map_ext; last by apply: seq_NoDup.
  move=> i1 /in_seq ? i2 /in_seq ? [].
  move: (Nat.eq_dec a1 a2) (Nat.eq_dec b1 b2) => [?|?] [?|?] /=; nia.
Qed.

Lemma multi_step_sub {i j x y z} :
  i <= j ->
  multi_step i x = Some y ->
  multi_step j x = Some z ->
  multi_step (j-i) y = Some z.
Proof.
  move=> ? Hi. rewrite [in multi_step j x](ltac:(lia) : j = i + (j - i)).
  by rewrite /multi_step iter_plus -/(multi_step _ _) Hi.
Qed.

(* from a config with the a really large value arrive at config with two large values *)
Lemma uniform_decision_aux2 x : ({l*(l+1) <= value1 x} + {l*(l+1) <= value2 x}) ->
  (bounded (l*l+1) x) + (not (uniformly_bounded M)) +
    { y | (exists k, k <= l*l /\ multi_step k x = Some y) /\ (l <= value1 y /\ l <= value2 y) }.
Proof.
  move=> Hlx.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (multi_step (l*l) x) (path (l*l) x).
  { move=> /loop_bounded H. left. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (multi_step (l*l+1) x) => [y|]; first last.
  { left. left. by apply: mortal_bounded. }
  pose P oz := if oz is Some z then 
    (if Hlx then l <= value2 z else l <= value1 z) else True.
  have HP : forall x, {P x} + {not (P x)}.
  { move=> [? /= |]; last by left. clear P.
    case: Hlx => ?; by apply: Compare_dec.le_dec. }
  have [|H'x] := Exists_dec P (path (l * l + 1) x) HP.
  { move=> /(Exists_sig P HP) [[z|]] [Hz /= H'z].
    - right. exists z. move: Hz => /In_pathE [k [? Hk]]. split.
      + exists k. split; [lia|done].
      + move: Hk => /multi_step_values_bound. clear P HP.
        case: Hlx H'z => /=; lia.
    - exfalso. by move: Hz Hxy => /In_None_pathE ->. }
  (* all value1 or value2 are smaller than l, not uniformly bounded *)
  left. right. subst P.
  have /(pigeonhole prod_nat_nat_eq_dec) : incl
    (map (fun oz => if oz is Some (p, (a, b)) then (if Hlx then (p, b) else (p, a)) else (0, 0)) (path (l * l + 1) x))
    (list_prod (seq 0 l) (seq 0 l)).
  { move=> [p c] /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(multi_step_k_monotone (l * l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [+ H]. have ? : not (l <= p').
    { move=> /nth_error_None Hp. move: H => /in_map_iff [k] [Hk /in_seq ?].
      have : multi_step (S k) x = None by rewrite /= Hk /step /= Hp.
      move=> /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    case: Hlx H'x HP => /= ? H'x HP.
    - move=> [? ?]. subst p c.
      move: H'x H => /Forall_Exists_neg /Forall_forall H /H{H} /= ?.
      apply /in_prod; apply /in_seq; lia.
    - move=> [? ?]. subst p c.
      move: H'x H => /Forall_Exists_neg /Forall_forall H /H{H} /= ?.
      apply /in_prod; apply /in_seq; lia. }
  apply: unnest. { rewrite map_length ?prod_length ?seq_length path_length. lia. }
  rewrite /path map_map. move=> /(dup_seq prod_nat_nat_eq_dec) [[i j]].
  move=> [+ ?].
  case Hi: (multi_step i x) => [[p [a1 b1]]|]; first last.
  { move: Hi => /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  case Hj: (multi_step j x) => [[p' [a2 b2]]|]; first last.
  { move: Hj => /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  clear H'x.
  have ? : not (p = p' /\ a1 = a2 /\ b1 = b2).
  { move=> [? [? ?]]. subst p' a2 b2.
    move: Hx. rewrite /path.
    have -> : l*l+1 = i + (S (j-i-1)) + (S (l*l -j)) by lia.
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_Config_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_Config_eq_dec _ _); [lia|done]. }
  case: Hlx HP => /= ? HP.
  - move=> [? ?]. subst p' b2.
    have ? : a1 <> a2 by lia.
    (* x ->>i (p, (a1, b1)) ->>(j-i) (p, (a2, b2)); a1 >= j-i or b1 >= j-i *)
    have ? : j-i <= a1.
    { move: Hi => /multi_step_values_bound /=. lia. }
    move: Hi Hj => /multi_step_sub H /H{H} /(_ ltac:(lia)).
    move /not_uniformly_boundedI. apply; lia.
  - move=> [? ?]. subst p' a2.
    have ? : b1 <> b2 by lia.
    have ? : j-i <= b1.
    { move: Hi => /multi_step_values_bound /=. lia. }
    move: Hi Hj => /multi_step_sub H /H{H} /(_ ltac:(lia)).
    move /not_uniformly_boundedI. apply; lia.
Qed.


(* from a config with two large values decide boundedness *)
Lemma uniform_decision_aux3 x : l <= value1 x -> l <= value2 x -> (bounded (l+1) x) + (not (uniformly_bounded M)).
Proof.
  move=> ??.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (multi_step (l) x) (path (l) x).
  { move=> /loop_bounded H. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (multi_step (l+1) x) => [y|]; first last.
  { left. by apply: mortal_bounded. }
  right. (* not uniformly bounded *)
  have /(pigeonhole Nat.eq_dec) : incl
    (map (fun oz => if oz is Some (p, (a, b)) then p else 0) (path (l + 1) x))
    (seq 0 l).
  { move=> p /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(multi_step_k_monotone (l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [->] H. apply /in_seq. suff : not (l <= p) by lia.
    move=> /nth_error_None Hp. move: H => /in_map_iff [k] [Hk /in_seq ?].
    have : multi_step (S k) x = None by rewrite /= Hk /step /= Hp.
    move=> /(multi_step_k_monotone (l+1)) /(_ ltac:(lia)).
    by rewrite Hxy. }
  apply: unnest. { rewrite map_length ?seq_length path_length. lia. }
  rewrite /path map_map. move=> /(dup_seq Nat.eq_dec) [[i j]].
  move=> [+ ?].
  case Hi: (multi_step i x) => [[p [a1 b1]]|]; first last.
  { move: Hi => /(multi_step_k_monotone (l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  case Hj: (multi_step j x) => [[p' [a2 b2]]|]; first last.
  { move: Hj => /(multi_step_k_monotone (l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  move=> ?. subst p'.
  have ? : a1 <> a2 \/ b1 <> b2.
  { suff : not (a1 = a2 /\ b1 = b2) by lia. move=> [??]. subst a2 b2.
    move: Hx. rewrite /path.
    have -> : l+1 = i + (S (j-i-1)) + (S (l -j)) by lia.
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_Config_eq_dec).
    move=> /(_ (Some (p, (a1, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_Config_eq_dec _ _); [lia|done]. }
  have ?: j - i <= a1 /\ j - i <= b1.
  { move: Hi => /multi_step_values_bound /=. lia. }
  move: Hi Hj => /multi_step_sub H /H{H} /(_ ltac:(lia)).
  move=> /not_uniformly_boundedI. apply; lia.
Qed.

Lemma uniformly_bounded_empty : uniformly_bounded [].
Proof.
  exists 1. move=> x. exists [x]. split; first done.
  move=> y [[|k]].
  - move=> [<-]. by left.
  - rewrite /= option_bind_iter /CM2.step.
    by case: (state x); rewrite /= iter_None.
Qed.

Lemma reaches_bounded {K k x y} : multi_step k x = Some y -> bounded K y -> bounded (k+K) x.
Proof.
  move=> Hxy /boundedE [HK|HK].
  - apply: loop_bounded.
    move: Hxy (Hxy) => /path_plus -> /multi_step_plus ->.
    apply /in_app_iff. by right.
  - apply: mortal_bounded.
    by move: Hxy => /multi_step_plus ->.
Qed.

Lemma uniform_decision : (uniformly_bounded M) + (not (uniformly_bounded M)).
Proof.
  wlog ? : /(l > 0).
  { move: (M) => [|? ?] /=.
    - move=> _. left. by apply: uniformly_bounded_empty.
    - apply. lia. }
  pose K := (l+1)*(l+1)*(l+1)*(l+1)*(l+1).
  (* test uniform boundedness by K ~ l^5 *)
  have [?|HK] := fixed_decision K. { left. by exists K. }
  right. move=> HM. apply: HK => x.
  (* x ->> y with at least one large counter *)
  have [|[y [[k1 [Hk1 Hxy]] ?]]] := uniform_decision_aux1 x.
  { apply: bounded_monotone. lia. }
  have -> : K = k1 + (K - k1) by lia.
  apply: (reaches_bounded Hxy).
  have : {l * (l + 1) <= value1 y} + {l * (l + 1) <= value2 y}.
  { case H: (l * (l + 1) - value1 y) => [|?]; [left|right]; lia. }
  move=> /uniform_decision_aux2 [[|]|[z]].
  - apply: bounded_monotone. lia.
  - by move=> /(_ HM).
  - move=> [[k2 [? Hyz]]] [/uniform_decision_aux3 H /H{H}].
    move=> [/bounded_monotone Hz|].
    + have -> : K - k1 = k2 + (K - k1 - k2) by lia.
      apply: (reaches_bounded Hyz). apply: Hz. lia.
    + by move=> /(_ HM).
Qed.

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
