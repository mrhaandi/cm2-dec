Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import CM2.CM2.

Lemma eq_or_inf {X: Type} : (forall (x y: X), {x = y} + {x <> y}) ->
  forall (x y: X) P, (x = y) \/ P -> (x = y) + P.
Proof.
  move=> H x y P. case: (H x y).
  - move=> ??. by left.
  - move=> ??. right. tauto.
Qed.

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma config_eta (x : Config) : x = (state x, (value1 x, value2 x)).
Proof. by move: x => [? [? ?]]. Qed.

Definition reversible (M : Cm2) : Prop := 
  forall x y z, step M x = Some z -> step M y = Some z -> x = y.


(* an avid instruction may jump to a valid state (except the first) *)
Inductive avid (l : nat) : Instruction -> Prop :=
  | avidI p b : S p < l -> avid l (dec b (S p)).

Section Reversible.
Variable M : Cm2.
Variable HM : reversible M.

(* a reversible machine has no avid instruction *)
Lemma reversible_not_avid : Forall (fun i => not (avid (length M) i)) M.
Proof.
  apply /Forall_Exists_neg => /Exists_nth [p] [j] [Hp].
  move Hip: (nth p M j) => ip H. move: H Hip => [q bp H'q] Hip.
  move Hiq: (nth q M j) => iq. have Hq: (q < length M) by lia. case: iq Hiq.
  - move: bp Hip => [] Hip [] Hiq.
    + suff: (p, (0, 2)) = (q, (0, 0)) by done.
      apply: (HM _ _ (S q, (0, 1))) => /=.
      all: by rewrite /step ?(nth_error_nth' _ j Hp) ?(nth_error_nth' _ j Hq) ?Hip ?Hiq.
    + suff: (p, (1, 1)) = (q, (0, 0)) by done.
      apply: (HM _ _ (S q, (1, 0))) => /=.
      all: by rewrite /step ?(nth_error_nth' _ j Hp) ?(nth_error_nth' _ j Hq) ?Hip ?Hiq.
    + suff: (p, (1, 1)) = (q, (0, 0)) by done.
      apply: (HM _ _ (S q, (0, 1))) => /=.
      all: by rewrite /step ?(nth_error_nth' _ j Hp) ?(nth_error_nth' _ j Hq) ?Hip ?Hiq.
    + suff: (p, (2, 0)) = (q, (0, 0)) by done.
      apply: (HM _ _ (S q, (1, 0))) => /=.
      all: by rewrite /step ?(nth_error_nth' _ j Hp) ?(nth_error_nth' _ j Hq) ?Hip ?Hiq.
  - move=> bq r Hiq.
    suff: (p, (if bp then (0, 1) else (1, 0))) = (q, (0, 0)) by clear; case: bp.
    apply: (HM _ _ (S q, (0, 0))) => /=.
    + rewrite /step (nth_error_nth' _ j Hp) Hip. clear. by case bp.
    + rewrite /step (nth_error_nth' _ j Hq) Hiq. clear. by case bq.
Qed.

(* partial two counter machine step function without jumps *)
Definition step' (x: Config) : option Config :=
  match nth_error M (state x) with
  | None => None (* halting configuration *)
  | Some (inc b) => (* increase counter, goto next state*)
    Some (1 + (state x), ((if b then 0 else 1) + (value1 x), (if b then 1 else 0) + (value2 x)))
  | Some (dec b y) => (* halt on jump *)
    if b then
      if value2 x is 0 then Some (1 + (state x), (value1 x, 0)) else None
    else
      if value1 x is 0 then Some (1 + (state x), (0, value2 x)) else None
  end.

Definition multi_step' (n: nat) (x: Config) : option Config :=
  Nat.iter n (option_bind step') (Some x).

Notation step := (CM2.step M).
Notation multi_step := (CM2.multi_step M).

(* reachability relation *)
Definition reaches' (x y: Config) := exists k, multi_step' k x = Some y.
Definition reaches (x y: Config) := exists k, multi_step k x = Some y.

(* step includes step' *)
Lemma step'_incl x y : step' x = Some y -> step x = Some y.
Proof.
  rewrite /step' /step. case: (nth_error M (state x)); last done.
  case; first done.
  move=> [] q; [by case: (value2 x)|by case: (value1 x)].
Qed.

(* multi_step includes multi_step' *)
Lemma multi_step'_incl k x y : multi_step' k x = Some y -> multi_step k x = Some y.
Proof.
  elim: k y; first done.
  move=> k /=. case: (multi_step' k x) => [y|]; last done.
  move=> /(_ y erefl) -> /=. by apply: step'_incl.
Qed.

(* reaches includes reaches' *)
Lemma reaches'_incl {x y} : reaches' x y -> reaches x y.
Proof. move=> [k /multi_step'_incl Hk]. by exists k. Qed.

Notation terminating := (CM2.terminating M).
Definition non_terminating x := forall k, multi_step k x <> None.

Lemma multi_step_plus k x k' y :
  multi_step k x = Some y -> multi_step (k + k') x = multi_step k' y.
Proof. rewrite /multi_step iter_plus. by move=> ->. Qed.

Lemma reaches'_step' x y : step' x = Some y -> reaches' x y.
Proof. move=> ?. by exists 1. Qed.

Lemma reaches_step {x y} : step x = Some y -> reaches x y.
Proof. move=> ?. by exists 1. Qed.

Lemma reaches'_trans {x y z} : reaches' x y -> reaches' y z -> reaches' x z.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k').
  by rewrite /multi_step' iter_plus -/(multi_step' k x) Hk.
Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k'). by move: Hk => /multi_step_plus ->.
Qed.

Lemma reaches_eq x y : x = y -> reaches x y.
Proof. move=> ->. by exists 0. Qed. 

Lemma multi_step_k_monotone {k x} k' :
  multi_step k x = None -> k <= k' -> multi_step k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
Qed.

Lemma reaches_terminating x y : reaches x y -> terminating y -> terminating x.
Proof.
  move=> [k /multi_step_plus Hk] [k' Hk']. exists (k+k'). by rewrite Hk.
Qed.

Lemma reaches_non_terminating x y : reaches x y -> non_terminating y -> non_terminating x.
Proof.
  move=> [k /multi_step_plus Hk] Hy k'.
  move=> /(multi_step_k_monotone (k+k')) /(_ ltac:(lia)).
  rewrite Hk. by apply: Hy.
Qed.

Lemma step_None x : step x = None <-> nth_error M (state x) = None.
Proof.
  rewrite /step. case: (nth_error M (state x)) => [i|]; last done.
  case: i; first done.
  by move: (value1 x) (value2 x) => [|?] [|?] [].
Qed.

Opaque nth_error.
Arguments nth_error_In {_ _ _ _}.

(* key lemma on the way to ensure that equivalent configurations behave identically
   every multi_step' computation without jumps increases the starting configuration
   (a > 0 -> value1 x > 0), (b > 0 -> value2 x > 0) in the same way *)
Lemma reaches'E x y : reaches' x y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      reaches' (state x, (a, b)) (state y, (a + n, b + m)).
Proof.
  move=> [k]. elim: k x y.
  { move=> x y [<-]. exists 0, 0. do 2 (split; first by lia).
    move=> a b ?? /=. exists 0. by rewrite ?Nat.add_0_r. }
  move=> k IH x y /=.
  case Hx': (multi_step' k x) => [x'|]; last done.
  move: Hx' => /IH [n] [m] [Hax'] [Hbx'] {}IH /=.
  rewrite /(step' x'). case Hi: (nth_error M (state x')) => [i|]; last done.
  move: i Hi => [].
  - move=> c Hi [<-] /=. exists ((if c then 0 else 1) + n), ((if c then 1 else 0) + m).
    split; first by lia. split; first by lia.
    move=> a b Ha Hb.
    have /reaches'_trans := IH a b ltac:(lia) ltac:(lia). apply.
    exists 1. rewrite /= /step' Hi /=.
    congr Some. congr pair. congr pair; lia.
  - move=> [] q Hi.
    + case H'bx': (value2 x') => [|bx']; last done.
      move=> [<-] /=. exists n, 0.
      split; first by lia. split; first by lia.
      move=> a b ??.
      have /reaches'_trans := IH a b ltac:(lia) ltac:(lia). apply.
      exists 1. rewrite /= /step' Hi. have ->: b + m = 0 by lia. 
      congr Some. congr pair. congr pair; lia.
    + case H'ax': (value1 x') => [|ax']; last done.
      move=> [<-] /=. exists 0, m.
      split; first by lia. split; first by lia.
      move=> a b ??.
      have /reaches'_trans := IH a b ltac:(lia) ltac:(lia). apply.
      exists 1. rewrite /= /step' Hi. have ->: a + n = 0 by lia.
      congr Some. congr pair. congr pair; lia.
Qed.

Lemma step'_inc_state x y :
  step' x = Some y -> state y = 1 + (state x).
Proof.
  rewrite /step'. case: (nth_error M (state x)); last done.
  move=> [].
  - by move=> c [/(f_equal state)] /= <-.
  - move: (value1 x) (value2 x) => [|?] [|?] [] _ //.
    all: by move=> [/(f_equal state)] /= <-.
Qed.

(* for a reversible machine for each configuration one can compute
   the number of steps until the first jump to 0 *)
Lemma reaches'I x : 
  { y | reaches' x y /\ 
    (if step y is Some z then state z = 0 \/ length M <= state z else True) }.
Proof.
  move Hn: (length M - state x) => n. elim: n x Hn.
  { move=> x ?. exists x. split; first by exists 0.
    rewrite /step. by have /nth_error_None -> : (length M <= state x) by lia. }
  move=> n IH x ?. case Hy: (step' x) => [y|].
  - move: (Hy) => /step'_inc_state ?.
    have /IH : (length M - state y = n) by lia.
    move=> [z] [? ?]. exists z. split; last done.
    move: Hy => /reaches'_step' /reaches'_trans. by apply.
  - exists x. split; first by exists 0.
    move: (reversible_not_avid) Hy => /Forall_forall.
    (* ad hoc, possibly externalize *)
    clear -HM. rewrite /step' /step. case Hi: (nth_error M (state x)) => [i|] H; last done.
    move: Hi => /nth_error_In /H {H}.
    move: i => []; first done. move=> [] q H.
    + move: (value2 x) => [|? ? /=]; first done.
      suff: not (q = S (q - 1) /\ S (q - 1) < length M) by lia.
      by move=> [+] /avidI => <-.
    + move: (value1 x) => [|? ? /=]; first done.
      suff: not (q = S (q - 1) /\ S (q - 1) < length M) by lia.
      by move=> [+] /avidI => <-.
Qed.

(* step with counters of same positivity *)
Lemma step_parallel {x y} x' :
  step x = Some y ->
  (state x = state x' /\ (value1 x > 0 <-> value1 x' > 0) /\ (value2 x > 0 <-> value2 x' > 0)) ->
  exists y', step x' = Some y' /\ 
  state y = state y' /\ 
  value1 x + value1 y' = value1 x' + value1 y /\
  value2 x + value2 y' = value2 x' + value2 y.
Proof.
  move=> + [Hx']. rewrite /step -Hx'. case: (nth_error M (state x)); last done.
  move=> [].
  { move=> c [<-] ?. eexists. split; [reflexivity|move=> /=; lia]. }
  move=> [] p.
  - case: (value2 x) => [|?] [<-] ?.
    + have ->: value2 x' = 0 by lia.
      eexists. split; [reflexivity|move=> /=; lia].
    + have ->: value2 x' = S ((value2 x') - 1) by lia.
      eexists. split; [reflexivity|move=> /=; lia].
  - case: (value1 x) => [|?] [<-] ?.
    + have ->: value1 x' = 0 by lia.
      eexists. split; [reflexivity|move=> /=; lia].
    + have ->: value1 x' = S ((value1 x') - 1) by lia.
      eexists. split; [reflexivity|move=> /=; lia].
Qed.

Lemma reaches'stepE {x y z} : reaches' x y -> step y = Some z ->
    forall a b, (value1 x > 0 <-> a > 0) -> (value2 x > 0 <-> b > 0) ->
      exists z', reaches (state x, (a, b)) z' /\
        state z = state z' /\
        value1 x + value1 z' = a + value1 z /\
        value2 x + value2 z' = b + value2 z.
Proof.
  move=> /reaches'E [n] [m] [?] [?] ++ a b ??.
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl Hxy.
  move=> /(step_parallel (state y, (a + n, b + m))) /=.
  move=> /(_ ltac:(lia)) [z'] [/reaches_step Hyz'] ?.
  exists z'. split; last by lia.
  exact: (reaches_trans Hxy Hyz').
Qed.

Lemma step_zero x a b : step x = Some (0, (a, b)) ->
  (value1 x = 1 + a /\ value2 x = b) \/ (value1 x = a /\ value2 x = 1 + b).
Proof.
  rewrite /step. case: (nth_error M (state x)); last done.
  case; first done.
  move=> [] q.
  - move: (value2 x) => [|?]; [done|case; lia].
  - move: (value1 x) => [|?]; [done|case; lia].
Qed.

Lemma reaches'_value_monotone x y :
  reaches' x y -> value1 x <= value1 y /\ value2 x <= value2 y.
Proof.
  move=> /reaches'E [n] [m] [?] [?].
  move=> /(_ (value1 x) (value2 x) ltac:(lia) ltac:(lia)). lia.
Qed.

(* if (1, 1) f->>t-> (0, 1 + m), then (a, b) t->> (0, a * m + b) *)
Lemma dec_a_0 {x m} : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (0, 1 + m)) ->
  forall a b, reaches (0, (a, b)) (0, (0, a * m + b)).
Proof.
  move=> H1x H2x. elim.
  - move=> b. by exists 0.
  - move=> a IH b. move: H1x => /reaches'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ (S a) b ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_trans. apply.
    have ->: m + a * m + b = a * m + (m + b) by lia.
    apply: (reaches_trans _ (IH (m + b))). exists 1.
    move: H2x. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    + move=> c [] /= -> ??. congr Some. congr pair. congr pair; lia.
    + move=> [] q.
      * move: (value2 x) Hbx => [|bx]; first by lia.
        rewrite Hax. move=> ? []. by lia.
      * move: (value1 x) Hax => [|ax]; first by lia.
        move=> ? [? ? ?] /=. subst. have ->: n' = 0 by lia.
        congr Some. congr pair. congr pair; lia.
Qed.

(* if (1, 1) f->>t-> (1 + n, 0), then (a, b) t->> (b * n + a, 0) *)
Lemma dec_b_0 {x n} : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (1 + n, 0)) ->
  forall a b, reaches (0, (a, b)) (0, (b * n + a, 0)).
Proof.
  move=> H1x H2x a b. elim: b a.
  - move=> a. by exists 0.
  - move=> b IH a. move: H1x => /reaches'E.
    move=> [n'] [m'] /= [Hax] [Hbx] /(_ a (S b) ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl /reaches_trans. apply.
    have ->: n + b * n + a = b * n + (n + a) by lia.
    apply: (reaches_trans _ (IH (n + a))). exists 1.
    move: H2x. simpl. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    + move=> c [] /= -> ??. congr Some. congr pair. congr pair; lia.
    + move=> [] q.
      * move: (value2 x) Hbx => [|bx]; first by lia.
        move=> ? [? ? ?] /=. subst. have ->: m' = 0 by lia.
        congr Some. congr pair. congr pair; lia.
      * move: (value1 x) Hax => [|ax]; first by lia.
        rewrite Hbx. move=> ? []. by lia.
Qed.

Lemma reaches'_zero {a b x} : reaches' (0, (a, b)) x -> 
  step x = Some (0, (0, 0)) ->
  forall a' b', (a' > 0 -> a > 0) -> (b' > 0 -> b > 0) ->
    reaches (0, (a', b')) (0, (0, 0)).
Proof.
  move=> H1x H2x a' b'. move Hc: (a'+b') => c. elim: c a' b' Hc.
  { move=> [|a'] [|b']; [|lia..]. move=> ???. by exists 0. }
  move=> c IH a' b' ???.
  have [?|?] : (a + b = 0) \/ (a + b > 0) by lia.
  { apply /reaches_eq. congr (_, (_, _)); lia. }
  move: (H2x) => /step_zero ?.
  have := reaches'stepE H1x H2x a' b'.
  move: (H1x) => /reaches'_value_monotone /= ?.
  move=> /(_ ltac:(lia) ltac:(lia)) [[pz [az bz]]] /= [Hz] [? ?].
  subst pz. have {}IH := IH az bz ltac:(lia) ltac:(lia) ltac:(lia).
  exact: (reaches_trans Hz IH).
Qed.

Lemma terminatingI {x y} : reaches x y -> step y = None -> terminating x.
Proof.
  move=> [k Hk] ?. exists (k+1). by move: Hk => /multi_step_plus ->.
Qed.

(* if (1, 1) ->> (S a, S b), then (a', b') does not terminate *)
Lemma reaches'_loop x n m : reaches' (0, (1, 1)) x -> 
  step x = Some (0, (1 + n, 1 + m)) ->
  forall a b, non_terminating (0, (a, b)).
Proof.
  move=> Hx H'x a b k. elim: k a b; first done.
  move=> k IH a b. have ->: S k = k + 1 by lia.
  move: Hx => /reaches'E [n'] [m'] /= [Hax] [Hbx].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl [k' Hk'].
  move=> /(multi_step_k_monotone (k'+(1+k))) /(_ ltac:(lia)).
  have : step (state x, (a + n', b + m')) = Some (0, (n + a, b + m)).
  {
    move: H'x. rewrite /= /step. case: (nth_error M (state x)); last done.
    move=> [].
    - move=> c [] /= -> ??. congr (Some (_, (_, _))); lia.
    - move=> [] q.
      + move: (value2 x) Hbx => [|bx] Hbx; first done.
        move=> [->] ?? /=.
        have ->: b + m' = S (b + m) by lia.
        congr (Some (_, (_, _))); lia.
      + move: (value1 x) Hax => [|ax] Hax; first done.
        move=> [->] ?? /=.
        have ->: a + n' = S (n + a) by lia.
        congr (Some (_, (_, _))); lia.
  }
  move: Hk' => /multi_step_plus -> /(multi_step_plus 1) ->.
  by apply: IH.
Qed.

(* x f->> HALT (without jumps) *)
Lemma reaches'_None_terminating x y :
  reaches' x y -> step y = None ->
  forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hxy /step_None Hy a b ? ?.
  move: Hxy => /reaches'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /reaches'_incl /terminatingI.
  apply. by apply /step_None.
Qed.

(* x f->>t-> HALT (with exactly one jump) *)
Lemma reaches'_Some_terminating x y z :
  reaches' x y -> step y = Some z -> length M <= state z ->
  forall a b, (value1 x > 0 <-> a > 0) -> (value2 x > 0 <-> b > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hxy Hy Hz a b ? ?.
  have [z' [Hz' ?]] := reaches'stepE Hxy Hy a b ltac:(lia) ltac:(lia).
  apply /(terminatingI Hz') /step_None /nth_error_None. lia.
Qed.

Lemma terminating_orI p a b x y : 
  reaches' (p, (S a, S b)) x ->
  step x = Some y ->
  length M <= state y ->
  (forall a', terminating (p, (S a', 0))) + (forall b', terminating (p, (0, S b'))).
Proof.
  rewrite /(step x). case Hi: (nth_error M (state x)) => [i|]; last done.
  move: i Hi => [].
  { (* inc instruction *)
    move=> c Hx H'x [/(f_equal state) /= H'y] ?. left=> a'.
    move: H'x => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /reaches'_incl [k Hk].
    exists (k+2). move: Hk => /multi_step_plus -> /=.
    rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= S (state x) by lia. }
  (* dec instruction *)
  move=> [] q Hx.
  - move=> +++ /ltac:(right).
    move=> /reaches'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> b'. move: Hk => /(_ 0 (S b') ltac:(lia) ltac:(lia)) [k Hk].
    exists (k+2).
    move: Hk => /multi_step'_incl /multi_step_plus -> /=.
    rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= q by lia.
  - move=> +++ /ltac:(left).
    move=> /reaches'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> a'. move: Hk => /(_ (S a') 0 ltac:(lia) ltac:(lia)) [k Hk].
    exists (k+2).
    move: Hk => /multi_step'_incl /multi_step_plus -> /=.
    rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= q by lia.
Qed.

Lemma transition_loop a b: 
  (forall a' b', (a > 0 <-> a' > 0) -> (b > 0 <-> b' > 0) -> 
     exists k a'' b'', multi_step k (0, (a', b')) = Some (0, (a'', b'')) /\
       k > 0 /\ (a' > 0 <-> a'' > 0) /\ (b' > 0 <-> b'' > 0)) ->
  non_terminating (0, (a, b)).
Proof.
  move=> H k. elim: k a b H; first done.
  move=> k IH a b Hab.
  have [k' [a' [b' [Hk' ?]]]] := Hab a b ltac:(done) ltac:(done).
  move=> /(multi_step_k_monotone (k' + k)) /(_  ltac:(lia)).
  move: Hk' => /multi_step_plus ->. apply: IH.
  move=> a'' b'' ? ?.
  have [? [? [? [? ?]]]] := Hab a'' b'' ltac:(lia) ltac:(lia).
  do 3 eexists. split; first by eassumption.
  by lia.
Qed.

(* uniform transition from equivalence class (0, 0) *)
Lemma transition_0_0 :
  (* terminating equivalence class (0, 0) *)
  (terminating (0, (0, 0))) +
  (* non-terminating equivalence class (0, 0) *)
  (non_terminating (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (exists a', reaches (0, (0, 0)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (exists b', reaches (0, (0, 0)) (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (exists a' b', reaches (0, (0, 0)) (0, (S a', S b'))).
Proof.
  have [y [Hxy]] := reaches'I (0, (0, 0)).
  case Hz: (step y) => [[pz [az bz]]|]; first last.
  { (* termination *)
    move=> _. do 4 left.
    move: Hxy => /reaches'_incl /terminatingI. by apply. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None H'z. do 4 left.
    move: Hxy => /reaches'_incl /reaches_trans H.
    move: Hz => /reaches_step /H /terminatingI. apply.
    by apply /step_None. }
  move=> /= ?. subst pz.
  move: az bz Hz => [|az] [|bz] Hz.
  - (* non-termination *) (* TODO still uses k *)
    do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
    move: Hxy => [k Hk]. exists (k+1), 0, 0.
    split; last by lia. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
    by move: Hk => /multi_step'_incl /multi_step_plus ->.
  - (* transition to (0, S b) *)
    do 1 left. right. exists bz.
    move: Hxy => /reaches'_incl /reaches_trans. apply. by apply: reaches_step.
  - (* transition to (S a, 0) *)
    do 2 left. right. exists az.
    move: Hxy => /reaches'_incl /reaches_trans. apply. by apply: reaches_step.
  - (* transition to (S a, S b) *)
    right. exists az, bz.
    move: Hxy => /reaches'_incl /reaches_trans. apply. by apply: reaches_step.
Qed.

Lemma terminatingE x : terminating x -> exists y, reaches x y /\ step y = None.
Proof.
  move=> [k Hk]. elim: k Hk; first done.
  move=> k IH /=. case Hy: (multi_step k x) => [y|].
  - move=> ?. exists y. split; [by exists k|done].
  - by move: Hy => /IH.
Qed.

(* uniform transition from equivalence class (S a, 0) *)
Lemma transition_Sa_0 :
  (* terminating equivalence class (S a, 0) *)
  (forall a, terminating (0, (S a, 0))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a, non_terminating (0, (S a, 0))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a, reaches (0, (S a, 0)) (0, (0, 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a, exists b', reaches (0, (S a, 0)) (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall a, exists a' b', reaches (0, (S a, 0)) (0, (S a', S b'))).
Proof.
  have := reaches'I (0, (1, 0)).
  move=> [x'] [Hx']. case H'x': (step x') => [y'|]; first last.
  { (* case: (1, 0) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a.
    move: Hx' => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a. apply: H => /=; lia. }
  move: y' H'x' => [py' [ay' [|by']]] + /= Hy'; subst py'.
  { (* case: (1, 0) f->>t-> (_, 0) *)
    move: ay' => [|ay'] H'x'.
    - (* case: (1, 0) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> a. apply: (reaches'_zero Hx' H'x'); lia.
    - (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) [k' Hk'].
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      subst pz. exists (k'+1), az, bz.
      move: Hk' Hz => /multi_step'_incl /multi_step_plus -> /= ->.
      split; [done|lia]. }
  move: ay' => [|ay'] H'x'; first last.
  { (* case: (1, 0) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> a.
    have := reaches'stepE Hx' H'x' (S a) 0.
    move=> /= /(_ ltac:(lia) ltac:(lia)) [[pz [az bz]]] /= [Hz ?].
    exists (a + ay'), by'. apply /(reaches_trans Hz) /reaches_eq.
    congr (_, (_, _)); lia. }
  (* case: (1, 0) f->>t-> (0, S b) *)
  have := reaches'I (0, (1, 1)).
  move=> [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [?|HS].
    { by do 4 left. }
    do 4 left. move=> [|a].
    { move: HS => /(_ by') /terminatingE [z] [Hz /terminatingI]. apply.
      exact: (reaches_trans (reaches_trans (reaches'_incl Hx') (reaches_step H'x')) Hz). }
    have := reaches'stepE Hx' H'x' (S (S a)) 0.
    move=> /= /(_ ltac:(lia) ltac:(lia)) [[pz [az bz]]] /= [Hz [? ?]]. subst pz.
    have := reaches'stepE Hx H'x az bz.
    move=> /= /(_ ltac:(lia) ltac:(lia)) [z'] [Hz' ?].
    apply: (terminatingI (reaches_trans Hz Hz')).
    apply /step_None /nth_error_None. lia. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: a'y b'y Ha'y Hb'y => [|a'y] [|b'y] H1y H2y.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    move: Hx H'x => /reaches'_value_monotone /= ?.
    rewrite (config_eta y) H0y => /step_zero. lia.
  - (* case: (1, 1) f->>t-> (0, S b') uniform transition to (0, Sb') *)
    do 1 left. right. move=> a.
    have := reaches'stepE Hx' H'x' (S a) 0.
    move=> /= /(_ ltac:(lia) ltac:(lia)) [[pz [az bz]]] /= [Hz [? ?]]. subst pz.
    have ? : y = (0, (0, S b'y)) by (rewrite (config_eta y); congr (_, (_, _))).
    subst y. have /(reaches_trans Hz) H := dec_a_0 Hx H'x az bz.
    exists (az * b'y + bz - 1). apply /(reaches_trans H) /reaches_eq.
    congr (_, (_, _)); lia.
  - (* case: (1, 1) f->>t-> (S a', 0) loop or uniform transition to (0, 0) *)
    move: Hx H'x. rewrite (config_eta y) H0y H1y H2y.
    move=> /dec_b_0 H /H {H}. move: a'y {H1y} => [|a'y] H.
    + (* uniform transition to (0, 0) *)
      do 2 left. right.
      suff: (forall a, reaches (0, (S a, 0)) (0, (a, 0))).
      { clear -HM. move=> H a. elim: (S a); first by exists 0.
        move=> {}a IH. have Hk' := H a. by apply: (reaches_trans (H a)). }
      move=> {}a.
      have := reaches'stepE Hx' H'x' (S a) 0.
      move=> /= /(_ ltac:(lia) ltac:(lia)) [[pz [az bz]]] /= [Hz [? ?]].
      subst pz. apply /(reaches_trans (reaches_trans Hz (H az bz))) /reaches_eq.
      congr (_, (_, _)); lia.
    + (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] /= [Hz] [? ?]. subst pz.
      move: Hk' => [k' Hk'].
      have [k'' Hk''] := H az bz.
      exists (k'+(1 + k'')), (bz * S a'y + az), 0.
      move: Hk' Hz Hk'' => /multi_step'_incl /multi_step_plus ->.
      move=> /(multi_step_plus 1) -> ->.
      split; first done. lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> a. apply: reaches'_loop; [eassumption|].
    by rewrite H'x (config_eta y) H0y H1y H2y.
Qed.

(* uniform transition from equivalence class (0, S b) *)
Lemma transition_0_Sb :
  (* terminating equivalence class *)
  (forall b, terminating (0, (0, S b))) +
  (* non-terminating equivalence class*)
  (forall b, non_terminating (0, (0, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall b, reaches (0, (0, S b)) (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall b, exists a', reaches (0, (0, S b)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall b, exists a' b', reaches (0, (0, S b)) (0, (S a', S b'))).
Proof.
Admitted.
(*
  have := reaches'I (0, (0, 1)).
  move=> [k'] [x'] [Hx']. case H'x': (step x') => [y'|]; first last.
  { (* case: (0, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx' => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (0, 1) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> b. apply: H => /=; lia. }
  move: y' H'x' => [py' [[|ay'] by']] + /= Hy'; subst py'.
  { (* case: (0, 1) f->>t-> (0, _) *)
    move: by' => [|by'] H'x'.
    - (* case: (0, 1) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> b. apply: dec_b_0'; first by eassumption.
      by rewrite H'x'.
    - (* non-termination *)
      do 3 left. right. move=> b. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      subst pz. exists (k'+1), az, bz.
      move: Hk' Hz => /multi_step'_incl /multi_step_plus -> /= ->.
      split; [done|lia]. }
  move: by' => [|by'] H'x'; first last.
  { (* case: (0, 1) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> b. exists (k'+1).
    move: Hx' => /reaches'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /multi_step'_incl.
    move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)).
    move=> [[pz' [az' bz']]] /= [Hz'] [? ?]. subst pz'.
    move=> Hx'. exists (az' - 1), (bz' - 1).
    move: Hx' Hz' => /multi_step_plus -> /= ->.
    congr Some. congr pair. congr pair; lia. }
  (* case: (0, 1) f->>t-> (S a, 0) *)
  have := reaches'I (0, (1, 1)).
  move=> [k] [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx => /reaches'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [HS|?]; last by (do 4 left).
    do 4 left. move=> [|b].
    { move: HS => /(_ ay') [k'' ?]. exists (k' + (1 + k'')).
      move: Hx' => /multi_step'_incl /multi_step_plus ->.
      by move: H'x' => /(multi_step_plus 1) ->. }
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S (S b)) ltac:(lia) ltac:(lia)).
    move: H'x' => /(step_parallel (state x', (n, S (S b) + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /=.
    move=> [Hz'] [?] ? Hx'.
    move: Hx => /reaches'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move: H'x => /(step_parallel (state x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)) [z] [Hz] [?] ? Hk.
    exists (k' + (1 + (k + (1 + 1)))).
    move: Hx' => /multi_step'_incl /multi_step_plus ->.
    move: Hz' => /(multi_step_plus 1) ->.
    have ->: pz' = 0 by lia. 
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    move: Hz => /(multi_step_plus 1) -> /=.
    apply /step_None /nth_error_None. by lia. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: b'y a'y Hb'y Ha'y => [|b'y] [|a'y] H2y H1y.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    move: Hx H'x => /not_transition_1_1_to_0_0.
    by rewrite (config_eta y) H0y H1y H2y.
  - (* case: (1, 1) f->>t-> (S a', 0) uniform transition to (S a', 0) *)
    do 1 left. right. move=> b.
    move: Hx' => /reaches'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)).
    move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)) [y'] [Hy'] [H0y'] ?.
    move=> /multi_step'_incl Hk'.
    move: Hx H'x => /dec_b_0 H. rewrite (config_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ (S ay') b) [k'' Hk''].
    exists (k' + (1 + k'')), (b * a'y + ay').
    move: Hk' Hy' Hk'' => /multi_step_plus -> /(multi_step_plus 1) ->.
    have ->: y' = (0, (S ay', b)).
    { rewrite (config_eta y') -H0y'. congr pair. congr pair; lia. }
    move=> ->. congr Some. congr pair. congr pair. lia.
  - (* case: (1, 1) f->>t-> (0, S b') loop or uniform transition to (0, 0) *)
    move: Hx H'x. rewrite (config_eta y) H0y H1y H2y.
    move=> /dec_a_0 H /H {H}. move: b'y {H2y} => [|b'y] H.
    + (* uniform transition to (0, 0) *)
      do 2 left. right.
      suff: (forall b, exists k, multi_step k (0, (0, S b)) = Some (0, (0, b))).
      { clear -HM. move=> H b. elim: (S b); first by exists 0.
        move=> {}b [k IH]. have [k' Hk'] := H b.
        exists (k'+k). by move: Hk' => /multi_step_plus ->. }
      move=> {}b.
      move: Hx' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /multi_step'_incl Hk'.
      move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      have [k''] := H (S ay') b. have ->: S ay' * 0 + b = b by lia.
      move=> Hk''. subst pz. exists (k' + (1 + k'')).
      move: Hk' => /multi_step_plus ->.
      move: Hz => /(multi_step_plus 1) ->.
      rewrite -Hk''. congr (multi_step k'' _). congr pair. congr pair; lia.
    + (* non-termination *)
      do 3 left. right. move=> b. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /reaches'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] /= [Hz] [? ?]. subst pz.
      have [k'' Hk''] := H az bz.
      exists (k'+(1 + k'')), 0, (az * S b'y + bz).
      move: Hk' Hz Hk'' => /multi_step'_incl /multi_step_plus ->.
      move=> /(multi_step_plus 1) -> ->.
      split; first done. lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> b. apply: reaches'_loop; [eassumption|].
    by rewrite H'x (config_eta y) H0y H1y H2y.
Qed.
*)

(* uniform transition from equivalence class (S a, S b) *)
Lemma transition_Sa_Sb :
  (* terminating equivalence class (S a, 0) *)
  (forall a b, terminating (0, (S a, S b))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a b, non_terminating (0, (S a, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a b, reaches (0, (S a, S b)) (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall a b, exists a', reaches (0, (S a, S b)) (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a b, exists b', reaches (0, (S a, S b)) (0, (0, S b'))).
Proof.
  have := reaches'I (0, (1, 1)).
  move=> [x] [Hk]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a b.
    move: H'x Hk => /reaches'_None_terminating H /H /=. apply; lia. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: H'x Hk => /reaches'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a b. apply: H => /=; lia. }
  move: y H'x => [py' [[|ay'] [|by']]] H'x /= Hy'; subst py'.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    move: Hk H'x => /reaches'_value_monotone /= ? /step_zero. lia.
  - (* case: (1, 1) f->>t-> (0, S b) uniform transition to (0, S b) *)
    right. move=> a b.
    move: Hk H'x => /dec_a_0 H /H /(_ (S a) (S b)) Hk'.
    exists (S a * by' + S b - 1).
    move: Hk'. congr (reaches _ _). congr pair. congr pair; lia.
  - (* case: (1, 1) f->>t-> (S a, 0) uniform transition to (S a, 0) *)
    do 1 left. right. move=> a b.  
    move: Hk H'x => /dec_b_0 H /H /(_ (S a) (S b)) Hk'.
    exists (S b * ay' + S a - 1).
    move: Hk'. congr (reaches _ _). congr pair. congr pair; lia.
  - (* case: (1, 1) f->>t-> (S a, S b) non-termination *)
    do 3 left. right. move=> a b.
    apply: reaches'_loop; by eassumption.
Qed.

(* equivalence class business *)

(* equivalence classes (0, 0), (S a, 0), (0, S b), (S a, S b) *)
Definition RZ '(a, b) '(a', b') : Prop := (a > 0 <-> a' > 0) /\ (b > 0 <-> b' > 0).

Definition representatives := [(0, 0); (1, 0); (0, 1); (1, 1)].

Lemma get_representative : forall ab, {v | In v representatives /\ RZ v ab}.
Proof.
  move=> [[|a] [|b]]; rewrite /representatives /RZ.
  - exists (0, 0) => /=. split; [tauto|lia].
  - exists (0, 1) => /=. split; [tauto|lia].
  - exists (1, 0) => /=. split; [tauto|lia].
  - exists (1, 1) => /=. split; [tauto|lia].
Qed.

Lemma multi_step_act k x y :
  multi_step k x = Some y -> x <> y -> multi_step (S (k - 1)) x = Some y.
Proof.
  case: k => [|k] /=; first by congruence.
  by rewrite Nat.sub_0_r.
Qed.

Lemma uniform_transition v :
  In v representatives -> 
  (* uniform termination *)
  (forall ab, RZ v ab -> terminating (0, ab)) +
  (* uniform non-termination *)
  (forall ab, RZ v ab -> non_terminating (0, ab)) +
  (* uniform transition *)
  {w | In w representatives /\ v <> w /\ 
    (forall ab, RZ v ab -> exists a'b', RZ w a'b' /\ reaches (0, ab) (0, a'b')) }.
Proof.
  rewrite /representatives /=.
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  case /HE; [|case /HE; [|case /HE; [|case /HE; last done]]] => <-.
  - have [[[[|]|]|]|] := transition_0_0 => H.
    + left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + left. right=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + right. exists (1, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      have [a'' ?] := H. exists (S a'', 0). split; by [|lia].
    + right. exists (0, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      have [b'' ?] := H. exists (0, S b''). split; by [|lia].
    + right. exists (1, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      have [a'' [b'' ?]] := H. exists (S a'', S b''). split; by [|lia].
  - have [[[[|]|]|]|] := transition_Sa_0 => H.
    + left. left=> - [a' b'] /= ?.
      have ->: a' = S (a'-1) by lia. have ->: b' = 0 by lia. done.
    + left. right=> - [a' b'] /= ?.
      have ->: a' = S (a'-1) by lia. have ->: b' = 0 by lia. done.
    + right. exists (0, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = 0 by lia.
      have ? := H (a'-1). exists (0, 0). split; by [|lia].
    + right. exists (0, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = 0 by lia.
      have [b'' ?] := H (a'-1). exists (0, S b''). split; by [|lia].
    + right. exists (1, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = 0 by lia.
      have [a'' [b'' ?]] := H (a'-1). exists (S a'', S b''). split; by [|lia].
  - have [[[[|]|]|]|] := transition_0_Sb => H.
    + left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b'-1) by lia. done.
    + left. right=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b'-1) by lia. done.
    + right. exists (0, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b'-1) by lia.
      have ? := H (b'-1). exists (0, 0). split; by [|lia].
    + right. exists (1, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b'-1) by lia.
      have [a'' ?] := H (b'-1). exists (S a'', 0). split; by [|lia].
    + right. exists (1, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b'-1) by lia.
      have [a'' [b'' ?]] := H (b'-1). exists (S a'', S b''). split; by [|lia].
  - have [[[[|]|]|]|] := transition_Sa_Sb => H.
    + left. left=> - [a' b'] /= ?.
      have ->: a' = S (a'-1) by lia. have ->: b' = S (b'-1) by lia. done.
    + left. right=> - [a' b'] /= ?.
      have ->: a' = S (a'-1) by lia. have ->: b' = S (b'-1) by lia. done.
    + right. exists (0, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = S (b'-1) by lia.
      have ? := H (a'-1) (b'-1). exists (0, 0). split; by [|lia].
    + right. exists (1, 0). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = S (b'-1) by lia.
      have [a'' ?] := H (a'-1) (b'-1). exists (S a'', 0). split; by [|lia].
    + right. exists (0, 1). split; [tauto|split;[done|]].
      move=> [a' b'] /= ?. have ->: a' = S (a'-1) by lia. have ->: b' = S (b'-1) by lia.
      have [b'' ?] := H (a'-1) (b'-1). exists (0, S b''). split; by [|lia].
Qed.


Arguments CM2.multi_step : simpl never.
Arguments incl_cons_inv {_ _ _ _}.

Lemma RZ_loop v : 
  (forall ab, RZ v ab ->
    exists k a'b', RZ v a'b' /\ multi_step (S k) (0, ab) = Some (0, a'b')) ->
  forall ab, RZ v ab -> non_terminating (0, ab).
Proof.
  move=> Hv ab Hab k. elim: k ab Hab; first done.
  move=> k IH ab /Hv [k'] [a'b'] [/IH] Hk Hk'.
  move=> /(multi_step_k_monotone (S k' + k)) /(_ ltac:(lia)).
  move: Hk' => /multi_step_plus ->. by apply: Hk.
Qed.

Lemma uniform_representative_decision v :
  In v representatives -> 
  (* uniform termination *)
  (forall ab, RZ v ab -> terminating (0, ab)) +
  (* uniform non-termination *)
  (forall ab, RZ v ab -> non_terminating (0, ab)).
Proof.
  move: v.
  have: { L & incl L representatives & 
    (forall v, In v representatives -> 
    (forall ab, RZ v ab -> terminating (0, ab)) + (forall ab, RZ v ab -> non_terminating (0, ab)) +
    { w | In w L /\ v <> w /\
      (forall ab, RZ v ab -> exists a'b', RZ w a'b' /\ reaches (0, ab) (0, a'b')) } ) }.
  { exists representatives; first done. by apply: uniform_transition. }
  case. elim.
  { move=> _ H v /H /= [[|]|]; [tauto|tauto|].
    by move=> [?] []. }
  move=> v0 L IH /incl_cons_inv [Hv0 HL] HRZ. apply: IH; first done.
  move=> v /HRZ. move=> [[|]|]; [tauto|tauto|].
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  move=> [w] /= [/HE [|]]; first last.
  { move=> ? [?] ?. right. by exists w. }
  move=> <- [Hvv0]. move: (Hv0) => /HRZ.
  move=> [[|]|].
  - (* termination *)
    move=> {}Hv0 Hv. left. left=> ab /Hv [a'b'] [/Hv0].
    by move=> /reaches_terminating H /H.
  - (* non-termination *)
    move=> {}Hv0 Hv. left. right=> ab /Hv [a'b'] [/Hv0].
    by move=> /reaches_non_terminating H /H.
  - (* chaining *)
    move=> [w'] /= [/HE [|]].
    + (* contradiction *)
      by move=> <- [].
    + move=> Hv [Hv0w' H'v0] H'v.
      have [|] : {v = w'} + {v <> w'} by do ? decide equality.
      * (* non-termination *)
        move=> ?. subst w'. left. right. apply: RZ_loop.
        move=> ab Hvab. move: (Hvab) => /H'v [a'b'] [Hv0a'b'].
        move: (Hv0a'b') => /H'v0 [a''b''] [Hva'b'].
        move=> [k' /multi_step_act Hk'] [k Hk].
        exists (k + (k' - 1)), a''b''. split; first done.
        have ->: S (k + (k' - 1)) = k + S (k' - 1) by lia.
        move: Hk => /multi_step_plus ->. apply: Hk'.
        move=> [?]. subst a''b''.
        have : RZ v v0.
        { move: Hva'b' Hv0a'b'. rewrite /RZ. clear.
          move: v v0 a'b' => [? ?] [? ?] [? ?]. lia. }
        move: Hv Hv0 Hvv0 => /HL. clear.
        rewrite /representatives /= /RZ. intuition (subst; by [|lia]).
      * move=> Hvw'. right. exists w'. split; first done.
        split; first done.
        move=> ab /H'v [a'b'] [/H'v0] [a''b''] [? H2] H1.
        exists a''b''. split; first done.
        apply: reaches_trans; by eassumption.
Qed.

Lemma uniform_decision_0 a b : (terminating (0, (a, b))) + (non_terminating (0, (a, b))).
Proof.
  have [v []] := get_representative (a, b).
  move=> /uniform_representative_decision [] => H /H; tauto.
Qed.

Lemma uniform_decision (x: Config) : (terminating x) + (non_terminating x).
Proof.
  have := reaches'I x.
  move=> [y] [Hxy].
  case Hz: (step y) => [[pz [az bz]]|] /=; first last.
  { (* termination *)
    move=> _. left. move: Hxy => /reaches'_incl /terminatingI. by apply. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None Hpz. left.
    have := reaches_trans (reaches'_incl Hxy) (reaches_step Hz).
    move=> /terminatingI. apply. by apply /step_None. }
  move=> ?. subst pz.
  case: (uniform_decision_0 az bz).
  - (* termination *)
    move=> + /ltac:(left).
    move=> /reaches_terminating. apply.
    exact: (reaches_trans (reaches'_incl Hxy) (reaches_step Hz)).
  - (* non-termination *)
    move=> + /ltac:(right).
    move=> /reaches_non_terminating. apply.
    exact: (reaches_trans (reaches'_incl Hxy) (reaches_step Hz)).
Qed.

End Reversible.

Check uniform_decision.
Print Assumptions uniform_decision.

(* decision procedure for the halting problem for reversible Cm2 *)
Definition decider (M: Cm2) (HM: reversible M) (c: Config) : bool :=
  match uniform_decision M HM c with
  | inl _ => true
  | inr _ => false
  end.

(* decision procedure correctness *)
Lemma decider_spec (M: Cm2) (HM: reversible M) (c: Config) :
  (decider M HM c = true) <-> (terminating M c).
Proof.
  rewrite /decider. case: (uniform_decision M HM c).
  - tauto.
  - move=> H. split; [done | by move=> [k /H]].
Qed.
