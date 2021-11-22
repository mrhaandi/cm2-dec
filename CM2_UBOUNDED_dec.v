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

Lemma pointwise_decision K x : {bounded K x} + {not (bounded K x)}.
Proof.
  case HK: (multi_step K x) => [y|].
  - have [Hy|Hy] := In_dec option_Config_eq_dec (Some y) (path K x).
    + left. apply: loop_bounded. by rewrite HK.
    + right. move=> [L [? HL]].
      apply: (pigeonhole option_Config_eq_dec (path (K+1) x) (map Some L)).
      * move=> [z|] /in_map_iff [k] [Hk] /in_seq ?.
        { apply /in_map_iff. exists z. split; first done.
          apply: HL. by exists k. }
        by move: Hk HK => /(multi_step_k_monotone K) /(_ ltac:(lia)) ->.
      * rewrite map_length path_length. lia.
      * apply /path_noloopI. by rewrite HK.
  - left. by apply: mortal_bounded.
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

Lemma bounded_monotone {k k' x} : k <= k' -> bounded k x -> bounded k' x.
Proof. move=> ? [L [? ?]]. exists L. split; [lia|done]. Qed.

Notation l := (length M).

Lemma lem1 x : let n := l*(l+1) in
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
  multi_step (n*k) (p, (a, n*k)) = Some (p, (a, n*b)).
Proof.
  move=> Hk. elim: n; first done.
  move=> n IH. rewrite /= /multi_step iter_plus -/(multi_step _ _).
  rewrite shift_multi_step_b; first by lia.
  rewrite Hk. have ->: b + n * k = n * k + b by lia.
  rewrite -/(multi_step _ _) shift_multi_step_b; first by lia.
  rewrite IH. congr (Some (_, (_, _))). lia.
Qed.


Lemma lem2 x : l*(l+1) <= value2 x -> (bounded (l*l+1) x) + (not (uniformly_bounded M)) +
  { y | (exists k, k <= l*l /\ multi_step k x = Some y) /\ (l <= value1 y /\ l <= value2 y) }.
Proof.
  move=> ?.
  have [|/path_noloopI Hx] :=
    In_dec option_Config_eq_dec (multi_step (l*l) x) (path (l*l) x).
  { move=> /loop_bounded H. left. left. apply: (bounded_monotone _ H). lia. }
  case Hxy: (multi_step (l*l+1) x) => [y|]; first last.
  { left. left. by apply: mortal_bounded. }
  pose P oz := if oz is Some z then l <= value1 z else True.
  have HP : forall x, {P x} + {not (P x)}.
  { move=> [?|]; last by left. by apply: Compare_dec.le_dec. }
  have [|H'x] := Exists_dec P (path (l * l + 1) x) HP.
  { move=> /(Exists_sig P HP) [[z|]] [Hz /= ?].
    - right. exists z. move: Hz => /In_pathE [k [? Hk]]. split.
      + exists k. split; [lia|done].
      + move: Hk => /multi_step_values_bound. lia.
    - exfalso. by move: Hz Hxy => /In_None_pathE ->. }
  (* all value1 are smaller than l, not uniformly bounded *)
  left. right => - [K HK].
  have /(pigeonhole prod_nat_nat_eq_dec) : incl
    (map (fun oz => if oz is Some (p, (a, b)) then (p, a) else (0, 0)) (path (l * l + 1) x))
    (list_prod (seq 0 l) (seq 0 l)).
  { move=> [p a] /in_map_iff [[[p' [a' b']]|]]; first last.
    { move=> [_ /In_pathE].
      move=> [?] [?] /(multi_step_k_monotone (l * l + 1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> [[-> ->]] H.
    have ? : not (l <= p).
    { move=> /nth_error_None Hp. move: H => /in_map_iff [k] [Hk /in_seq ?].
      have : multi_step (S k) x = None by rewrite /= Hk /step /= Hp.
      move=> /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move: H'x H => /Forall_Exists_neg /Forall_forall H /H{H} /= ?.
    apply /in_prod; apply /in_seq; lia. }
  apply: unnest. { rewrite map_length ?prod_length ?seq_length path_length. lia. }
  rewrite /path map_map. move=> /(dup_seq prod_nat_nat_eq_dec) [[i j]].
  move=> [+ ?].
  case Hi: (multi_step i x) => [[p [a b1]]|]; first last.
  { move: Hi => /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  case Hj: (multi_step j x) => [[p' [a' b2]]|]; first last.
  { move: Hj => /(multi_step_k_monotone (l*l+1)) /(_ ltac:(lia)). by rewrite Hxy. }
  move=> [? ?]. subst p' a'.
  have ? : b1 <> b2.
  { move=> ?. subst b2.
    move: Hx. rewrite /path.
    have -> : l*l+1 = i + (S (j-i-1)) + (S (l*l -j)) by lia.
    rewrite seq_app seq_app /= ?map_app /= (NoDup_count_occ option_Config_eq_dec).
    move=> /(_ (Some (p, (a, b1)))). have ->: i + S (j - i - 1) = j by lia.
    rewrite Hi Hj ?count_occ_app /=. case: (option_Config_eq_dec _ _); [lia|done]. }
  (* x ->>i (p, (a, b1)) ->>(j-i) (p, (a, b2)); b1 >= j-i *)
  have ? : j-i <= b1.
  { move: Hi => /multi_step_values_bound /=. lia. }
  USE shift_multi_step_k_b
  (* TODO general lemma for not uniformly bounded becuase arbitrary long semi-loop *)
Admitted.


Lemma uniform_decision : (uniformly_bounded M) + (not (uniformly_bounded M)).
Proof.
  (*
  wlog : /(0 < l).
  { case: (M) => [/=|? ?].
    - move=> _. left. exists 1. move=> x.
      exists [x]. split; first done.
      move=> y [[|k]].
      + move=> [<-]. by left.
      + rewrite /CM2.multi_step /= option_bind_iter /CM2.step.
        case: (state x); by rewrite /= iter_None.
    - apply. move=> /=. lia. } *)
  (* inspect large counter values *)
  have := Forall_dec (fun p => In (multi_step l (p, (l, l))) (None :: path l (p, (l, l)))) _ (seq 0 l).
  apply: unnest. { move=> ?. by apply: (In_dec option_Config_eq_dec). }
  move=> [Hl|H]; first last.
  { (* nur uniformly bounded *)
    right => - [K HK]. apply: H. apply /Forall_forall.
    move=> p /in_seq ?.
    apply: Decidable.not_not.
    { apply: In_decidable. admit. (* easy *) }
    case Hxy: (multi_step l (p, (l, l))) => [y|/=]; last by tauto.
    move=> /= /Decidable.not_or [_].
    rewrite -Hxy => /path_noloopI.
    admit. (* very hard *) }
  (* now large configurations are uniformly bounded by l *)
  have := Forall_dec 
    (fun x => In (multi_step l x) (None :: path (l*l) x)) _ 
    (list_prod (seq 0 l) (list_prod (seq 0 (l*l+1)) (seq 0 (l*l+1)))).
  apply: unnest. { move=> ?. by apply: (In_dec option_Config_eq_dec). }
  move=> [Hll|H]; first last.
  { admit. (* very hard *) }
  left.
  exists (l*l*l*l*l+l*l+l).
  move=> [p [a b]].
  have [Hp|?] : l <= p \/ p < l by lia.
  { exists [(p, (a, b))].  }
  have [?|[?|?]] : (l <= a /\ l <= b) \/ (a < l \/ b < l) by lia.
  - move: Hl => /Forall_forall /(_ p).
    apply: unnest. { apply /in_seq. lia. }
    move=> /= [/esym Hp|Hp].
    + apply: (@bounded_monotone l); first by lia.
      apply: mortal_bounded.
      have ->: a = l + (a-l) by lia. have ->: b = l + (b-l) by lia.
      rewrite shift_multi_step_a; first by lia.
      rewrite shift_multi_step_b; first by lia.
      by rewrite Hp.
    + have : In (multi_step l (p, (a, b))) (path l (p, (a, b))).
      { move: Hp => /in_map_iff [k] [Hk ?].
        apply /in_map_iff. exists k. split; last done.
          }

      exists (map (fun oy => if oy is Some y then y else (p, (a, b))) (path (l+1) (p, (a, b)))).
      split. { rewrite map_length path_length. nia. }
      move=> y [k].
      have ->: a = l + (a-l) by lia. have ->: b = l + (b-l) by lia.
      rewrite shift_path_a shift_path_b.
      move=> /mortal_bounded.
    
    move=> /esym /mortal_bounded.
      apply.

  wlog : /(l <= a \/ l )
  
    Search (not (_ \/ _)).
    move=> /= /.
move=> x y.
rewrite /Decidable.decidable.
    Check In_decidable.
    Search ((_ -> False) -> False).
    Search (not (not _)).   
  }
have [?|H] := fixed_decision (l*l*l*l*l+l*l+l).
  { left. eexists. by eassumption. }
  right. move=> [K HK]. apply: H => x.

  have [L ?] := HK x.
  move=> /(_ x) in HK.

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
