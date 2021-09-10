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

Notation terminating := (CM2.terminating M).
Definition non_terminating x := forall k, multi_step k x <> None.

Lemma multi_step_plus k x k' y :
  multi_step k x = Some y -> multi_step (k + k') x = multi_step k' y.
Proof. rewrite /multi_step iter_plus. by move=> ->. Qed.

Lemma multi_step_k_monotone {k x} k' : multi_step k x = None -> k <= k' -> multi_step k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
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
Lemma multi_step'E k x y : multi_step' k x = Some y ->
  exists n m, value1 y = value1 x + n /\ value2 y = value2 x + m /\ 
    forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) ->
      multi_step' k (state x, (a, b)) = Some (state y, (a + n, b + m)).
Proof.
  elim: k x y.
  { move=> x y [<-]. exists 0, 0. do 2 (split; first by lia).
    move=> a b ?? /=. by rewrite ?Nat.add_0_r. }
  move=> k IH x y /=.
  case Hx': (multi_step' k x) => [x'|]; last done.
  move: Hx' => /IH [n] [m] [Hax'] [Hbx'] {}IH /=.
  rewrite /(step' x'). case Hi: (nth_error M (state x')) => [i|]; last done.
  move: i Hi => [].
  - move=> c Hi [<-] /=. exists ((if c then 0 else 1) + n), ((if c then 1 else 0) + m).
    split; first by lia. split; first by lia.
    move=> a b Ha Hb. rewrite IH; [done|done|].
    rewrite /= /step' Hi /=. congr Some. congr pair. congr pair; lia.
  - move=> [] q Hi.
    + case H'bx': (value2 x') => [|bx']; last done.
      move=> [<-] /=. exists n, 0.
      split; first by lia. split; first by lia.
      move=> a b ??. rewrite IH; [done|done|].
      rewrite /step' /= Hi. have ->: b + m = 0 by lia. 
      congr Some. congr pair. congr pair; lia.
    + case H'ax': (value1 x') => [|ax']; last done.
      move=> [<-] /=. exists 0, m.
      split; first by lia. split; first by lia.
      move=> a b ??. rewrite IH; [done|done|].
      rewrite /step' /= Hi. have ->: a + n = 0 by lia.
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
Lemma multi_step'I x : 
  { k & { y | multi_step' k x = Some y /\ 
    (if step y is Some z then state z = 0 \/ length M <= state z else True) } }.
Proof.
  move Hn: (length M - state x) => n. elim: n x Hn.
  { move=> x ?. exists 0, x. split; first done.
    rewrite /step. by have /nth_error_None -> : (length M <= state x) by lia. }
  move=> n IH x ?. case Hy: (step' x) => [y|].
  - move: (Hy) => /step'_inc_state ?.
    have /IH : (length M - state y = n) by lia.
    move=> [k] [z] [? ?]. exists (1+k), z.
    split; last done.
    by rewrite /multi_step' iter_plus /= Hy.
  - exists 0, x. split; first done.
    move: (reversible_not_avid) Hy => /Forall_forall.
    (* ad hoc, possibly externalize *)
    clear -HM. rewrite /step' /step. case Hi: (nth_error M (state x)) => [i|] H; last done.
    move: Hi => /nth_error_In /H {H}.
    move: i => []; first done.
    move=> [] q H.
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

(* if (1, 1) f->>t-> (0, 1 + m), then (a, b) t->> (0, a * m + b) *)
Lemma dec_a_0 k x m : multi_step' k (0, (1, 1)) = Some x -> 
  step x = Some (0, (0, 1 + m)) ->
  forall a b, exists k', multi_step k' (0, (a, b)) = Some (0, (0, a * m + b)).
Proof.
  move=> H1x H2x. elim.
  - move=> b. by exists 0.
  - move=> a IH b. move: H1x => /multi_step'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ (S a) b ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl Hk.
    have [k' {}IH] := IH (m + b).
    exists (k + (1 + k')).
    move: Hk => /multi_step_plus ->.
    have ->: m + a * m + b = a * m + (m + b) by lia.
    rewrite <- IH. apply: multi_step_plus.
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
Lemma dec_b_0 k x n : multi_step' k (0, (1, 1)) = Some x -> 
  step x = Some (0, (1 + n, 0)) ->
  forall a b, exists k', multi_step k' (0, (a, b)) = Some (0, (b * n + a, 0)).
Proof.
  move=> H1x H2x a b. elim: b a.
  - move=> a. by exists 0.
  - move=> b IH a. move: H1x => /multi_step'E.
    move=> [n'] [m'] /= [Hax] [Hbx] /(_ a (S b) ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl Hk.
    have [k' {}IH] := IH (n + a). exists (k + (1 + k')).
    move: Hk => /multi_step_plus ->.
    have ->: n + b * n + a = b * n + (n + a) by lia.
    rewrite <- IH. apply: multi_step_plus.
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

(* if (1, 0) f->>t-> (0, 0), then (a, 0) t->> (0, 0) *)
Lemma dec_a_0' k x : multi_step' k (0, (1, 0)) = Some x -> 
  step x = Some (0, (0, 0)) ->
  forall a, exists k', multi_step k' (0, (a, 0)) = Some (0, (0, 0)).
Proof.
  move=> H1x H2x. elim; first by exists 0.
  move=> a [k' IH]. move: H1x => /multi_step'E.
  move=> [n'] [m'] /= [Hax] [Hbx] /(_ (S a) 0 ltac:(lia) ltac:(lia)).
  move=> /multi_step'_incl Hk.
  exists (k + (1 + k')).
  move: Hk => /multi_step_plus ->.
  rewrite <- IH. apply: multi_step_plus.
  move: H2x => /(step_parallel (state x, (S a + n', m'))) /= /(_ ltac:(lia)).
  move=> [[pz [az bz]]] [->] /= [<-] ?.
  congr (Some (_, (_, _))); lia.
Qed.

(* if (0, 1) f->>t-> (0, 0), then (0, b) t->> (0, 0) *)
Lemma dec_b_0' k x : multi_step' k (0, (0, 1)) = Some x -> 
  step x = Some (0, (0, 0)) ->
  forall b, exists k', multi_step k' (0, (0, b)) = Some (0, (0, 0)).
Proof.
  move=> H1x H2x. elim; first by exists 0.
  move=> b [k' IH]. move: H1x => /multi_step'E.
  move=> [n'] [m'] /= [Hax] [Hbx] /(_ 0 (S b) ltac:(lia) ltac:(lia)).
  move=> /multi_step'_incl Hk.
  exists (k + (1 + k')).
  move: Hk => /multi_step_plus ->.
  rewrite <- IH. apply: multi_step_plus.
  move: H2x => /(step_parallel (state x, (n', S b + m'))) /= /(_ ltac:(lia)).
  move=> [[pz [az bz]]] [->] /= [<-] ?.
  congr (Some (_, (_, _))); lia.
Qed.

(* if (1, 1) ->> (S a, S b), then (a', b') does not terminate *)
Lemma dec_loop k x n m : multi_step' k (0, (1, 1)) = Some x -> 
  step x = Some (0, (1 + n, 1 + m)) ->
  forall a b, non_terminating (0, (a, b)).
Proof.
  move=> Hk Hx.
  move=> a b k' /(multi_step_k_monotone (k' * S k)) /(_ ltac:(lia)).
  elim: k' a b; first done.
  move=> k' IH a b. have ->: S k' * S k = (k + 1) + (k' * S k) by lia.
  have : multi_step (k + 1) (0, (a, b)) = Some (0, (n + a, b + m)).
  {
    move: Hk => /multi_step'E [n'] [m'] /= [Hax] [Hbx].
    move=> /(_ a b ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl /multi_step_plus ->.
    move: Hx. rewrite /= /step. case: (nth_error M (state x)); last done.
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
    move=> /multi_step_plus ->. by apply: IH.
Qed.

(* x f->> HALT (without jumps) *)
Lemma multi_step'_None_terminating k x y :
  multi_step' k x = Some y -> step y = None ->
  forall a b, (a > 0 -> value1 x > 0) -> (b > 0 -> value2 x > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hx /step_None Hy a b ? ?. exists (1+k).
  move: Hx => /multi_step'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /multi_step'_incl ->.
  by apply /step_None.
Qed.

(* x f->>t-> HALT (with exactly one jump) *)
Lemma multi_step'_Some_terminating k x y z :
  multi_step' k x = Some y -> step y = Some z -> length M <= state z ->
  forall a b, (value1 x > 0 <-> a > 0) -> (value2 x > 0 <-> b > 0) -> 
    terminating (state x, (a, b)).
Proof.
  move=> Hx Hy Hz a b ? ?. exists (2+k).
  move: Hx => /multi_step'E [n] [m] /= [?] [?].
  move=> /(_ a b ltac:(lia) ltac:(lia)) /multi_step'_incl ->.
  move: Hy => /(step_parallel (state y, (a + n, b + m))) /= /(_ ltac:(lia)).
  move=> [[pz [az bz]]] [->] /= [<-] ?.
  by apply /step_None /nth_error_None.
Qed.

Lemma terminating_orI k p a b x y : 
  multi_step' k (p, (S a, S b)) = Some x ->
  step x = Some y ->
  length M <= state y ->
  (forall a', terminating (p, (S a', 0))) + (forall b', terminating (p, (0, S b'))).
Proof.
  rewrite /(step x). case Hi: (nth_error M (state x)) => [i|]; last done.
  move: i Hi => [].
  { (* inc instruction *)
    move=> c Hx H'x [/(f_equal state) /= H'y] ?. left=> a'.
    move: H'x => /multi_step'E [n] [m] /= [?] [?].
    move=> /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl Hk.
    exists (k+2). move: Hk => /multi_step_plus -> /=.
    rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= S (state x) by lia. }
  (* dec instruction *)
  move=> [] q Hx.
  - move=> +++ /ltac:(right).
    move=> /multi_step'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> b'. exists (k+2). move: Hk => /(_ 0 (S b') ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl /multi_step_plus -> /=.
    rewrite /step /= Hx /=.
    by have /nth_error_None -> : length M <= q by lia.
  - move=> +++ /ltac:(left).
    move=> /multi_step'E [n] [m] /= [->] [->] Hk.
    move=> [/(f_equal state)] /= <- ?.
    move=> a'. exists (k+2). move: Hk => /(_ (S a') 0 ltac:(lia) ltac:(lia)).
    move=> /multi_step'_incl /multi_step_plus -> /=.
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

(* not (1, 1) f->>t-> (0, 0) *)
Lemma not_transition_1_1_to_0_0 k x : multi_step' k (0, (1, 1)) = Some x -> step x <> Some (0, (0, 0)).
Proof.
  move=> /multi_step'E [n] [m] /= [H1x] [H2x] _.
  rewrite /step. case: (nth_error M (state x)); last done.
  move=> [].
  - move=> ? [] ?. lia.
  - move=> [] ?; rewrite ?H1x ?H2x; case; lia.
Qed.

(* uniform transition from equivalence class (0, 0) *)
Lemma transition_0_0 :
  (* terminating equivalence class (0, 0) *)
  (terminating (0, (0, 0))) +
  (* non-terminating equivalence class (0, 0) *)
  (non_terminating (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (exists k a', multi_step k (0, (0, 0)) = Some (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (exists k b', multi_step k (0, (0, 0)) = Some (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (exists k a' b', multi_step k (0, (0, 0)) = Some (0, (S a', S b'))).
Proof.
  have [k [y [Hk]]] := multi_step'I (0, (0, 0)).
  case Hz: (step y) => [[pz [az bz]]|]; first last.
  { (* termination *)
    move=> _. do 4 left. exists (k+1).
    by move: Hk => /multi_step'_incl /multi_step_plus ->. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None H'z. do 4 left. exists (k+(1+1)).
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    move: Hz => /(multi_step_plus 1) ->.
    by rewrite /= /step H'z. }
  move=> /= ?. subst pz.
  move: az bz Hz => [|az] [|bz] Hz.
  - (* non-termination *)
    do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
    exists (k+1), 0, 0.
    split; last by lia. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
    by move: Hk => /multi_step'_incl /multi_step_plus ->.
  - (* transition to (0, S b) *)
    do 1 left. right. exists (k+1), bz.
    by move: Hk => /multi_step'_incl /multi_step_plus ->.
  - (* transition to (S a, 0) *)
    do 2 left. right. exists (k+1), az.
    by move: Hk => /multi_step'_incl /multi_step_plus ->.
  - (* transition to (S a, S b) *)
    right. exists (k+1), az, bz.
    by move: Hk => /multi_step'_incl /multi_step_plus ->.
Qed.

(* uniform transition from equivalence class (S a, 0) *)
Lemma transition_Sa_0 :
  (* terminating equivalence class (S a, 0) *)
  (forall a, terminating (0, (S a, 0))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a, non_terminating (0, (S a, 0))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a, exists k, multi_step k (0, (S a, 0)) = Some (0, (0, 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a, exists k b', multi_step k (0, (S a, 0)) = Some (0, (0, S b'))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall a, exists k a' b', multi_step k (0, (S a, 0)) = Some (0, (S a', S b'))).
Proof.
  have := multi_step'I (0, (1, 0)).
  move=> [k'] [x'] [Hx']. case H'x': (step x') => [y'|]; first last.
  { (* case: (1, 0) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a. move: Hx' => /multi_step'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /multi_step'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a. apply: H => /=; lia. }
  move: y' H'x' => [py' [ay' [|by']]] + /= Hy'; subst py'.
  { (* case: (1, 0) f->>t-> (_, 0) *)
    move: ay' => [|ay'] H'x'.
    - (* case: (1, 0) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> a. apply: dec_a_0'; first by eassumption.
      by rewrite H'x'.
    - (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /multi_step'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      subst pz. exists (k'+1), az, bz.
      move: Hk' Hz => /multi_step'_incl /multi_step_plus -> /= ->.
      split; [done|lia]. }
  move: ay' => [|ay'] H'x'; first last.
  { (* case: (1, 0) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> a. exists (k'+1).
    move: Hx' => /multi_step'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /multi_step'_incl.
    move: H'x' => /(step_parallel (state x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /= [Hz'] [? ?].
    subst pz'. move=> Hx'. exists (az' - 1), (bz' - 1).
    move: Hx' Hz' => /multi_step_plus -> /= ->.
    congr Some. congr pair. congr pair; lia. }
  (* case: (1, 0) f->>t-> (0, S b) *)
  have := multi_step'I (0, (1, 1)).
  move=> [k] [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a. move: Hx => /multi_step'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [?|HS]; first by (do 4 left).
    do 4 left. move=> [|a].
    { move: HS => /(_ by') [k'' ?]. exists (k' + (1 + k'')).
      move: Hx' => /multi_step'_incl /multi_step_plus ->.
      by move: H'x' => /(multi_step_plus 1) ->. }
    move: Hx' => /multi_step'E [n] [m] /= [?] [?].
    move=> /(_ (S (S a)) 0 ltac:(lia) ltac:(lia)).
    move: H'x' => /(step_parallel (state x', (S (S a) + n, m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /=.
    move=> [Hz'] [?] ? Hx'.
    move: Hx => /multi_step'E [n'] [m'] /= [?] [?].
    move=> /(_ az' bz' ltac:(lia) ltac:(lia)).
    move: H'x => /(step_parallel (state x, (az' + n', bz' + m'))) /=.
    move=> /(_ ltac:(lia)).
    move=> [z] [Hz] [?] ? Hk. exists (k' + (1 + (k + (1 + 1)))).
    move: Hx' => /multi_step'_incl /multi_step_plus ->.
    move: Hz' => /(multi_step_plus 1) ->.
    have ->: pz' = 0 by lia. 
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    move: Hz => /(multi_step_plus 1) -> /=.
    apply /step_None /nth_error_None. by lia. }
  (* case (1, 1) f->>t-> (a, b) at index 0 *)
  move=> H0y. move Ha'y: (value1 y) => a'y. move Hb'y: (value2 y) => b'y.
  move: a'y b'y Ha'y Hb'y => [|a'y] [|b'y] H1y H2y.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    move: Hx H'x => /not_transition_1_1_to_0_0.
    by rewrite (config_eta y) H0y H1y H2y.
  - (* case: (1, 1) f->>t-> (0, S b') uniform transition to (0, Sb') *)
    do 1 left. right. move=> a.
    move: Hx' => /multi_step'E [n] [m] /= [?] [?].
    move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)).
    move: H'x' => /(step_parallel (state x', (S a + n, m))) /=.
    move=> /(_ ltac:(lia)) [y'] [Hy'] [H0y'] ?.
    move=> /multi_step'_incl Hk'.
    move: Hx H'x => /dec_a_0 H. rewrite (config_eta y) H0y H1y H2y.
    move=> /H {H} => /(_ a (S by')) [k'' Hk''].
    exists (k' + (1 + k'')), (a * b'y + by').
    move: Hk' Hy' Hk'' => /multi_step_plus -> /(multi_step_plus 1) ->.
    have ->: y' = (0, (a, S by')).
    { rewrite (config_eta y') -H0y'. congr pair. congr pair; lia. }
    move=> ->. congr Some. congr pair. congr pair. lia.
  - (* case: (1, 1) f->>t-> (S a', 0) loop or uniform transition to (0, 0) *)
    move: Hx H'x. rewrite (config_eta y) H0y H1y H2y.
    move=> /dec_b_0 H /H {H}. move: a'y {H1y} => [|a'y] H.
    + (* uniform transition to (0, 0) *)
      do 2 left. right.
      suff: (forall a, exists k, multi_step k (0, (S a, 0)) = Some (0, (a, 0))).
      { clear -HM. move=> H a. elim: (S a); first by exists 0.
        move=> {}a [k IH]. have [k' Hk'] := H a.
        exists (k'+k). by move: Hk' => /multi_step_plus ->. }
      move=> {}a.
      move: Hx' => /multi_step'E [n] [m] /= [?] [?].
      move=> /(_ (S a) 0 ltac:(lia) ltac:(lia)) /multi_step'_incl Hk'.
      move: H'x' => /(step_parallel (state x', (S a + n, m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      have [k''] := H a (S by'). have ->: S by' * 0 + a = a by lia.
      move=> Hk''. subst pz. exists (k' + (1 + k'')).
      move: Hk' => /multi_step_plus ->.
      move: Hz => /(multi_step_plus 1) ->.
      rewrite -Hk''. congr (multi_step k'' _). congr pair. congr pair; lia.
    + (* non-termination *)
      do 3 left. right. move=> a. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /multi_step'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] /= [Hz] [? ?]. subst pz.
      have [k'' Hk''] := H az bz.
      exists (k'+(1 + k'')), (bz * S a'y + az), 0.
      move: Hk' Hz Hk'' => /multi_step'_incl /multi_step_plus ->.
      move=> /(multi_step_plus 1) -> ->.
      split; first done. lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> a. apply: dec_loop; [eassumption|].
    by rewrite H'x (config_eta y) H0y H1y H2y.
Qed.

(* uniform transition from equivalence class (0, S b) *)
Lemma transition_0_Sb :
  (* terminating equivalence class *)
  (forall b, terminating (0, (0, S b))) +
  (* non-terminating equivalence class*)
  (forall b, non_terminating (0, (0, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall b, exists k, multi_step k (0, (0, S b)) = Some (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall b, exists k a', multi_step k (0, (0, S b)) = Some (0, (S a', 0))) +
  (* uniform transition to equivalence class (S a, S b) *)
  (forall b, exists k a' b', multi_step k (0, (0, S b)) = Some (0, (S a', S b'))).
Proof.
  have := multi_step'I (0, (0, 1)).
  move=> [k'] [x'] [Hx']. case H'x': (step x') => [y'|]; first last.
  { (* case: (0, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx' => /multi_step'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (0, 1) f->>t-> HALT; uniform termination *)
    move: Hx' H'x' => /multi_step'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> b. apply: H => /=; lia. }
  move: y' H'x' => [py' [[|ay'] by']] + /= Hy'; subst py'.
  { (* case: (0, 1) f->>t-> (0, _) *)
    move: by' => [|by'] H'x'.
    - (* case: (0, 1) f->>t-> (0, 0) uniform transition to (0, 0) *)
      do 2 left. right. move=> b. apply: dec_b_0'; first by eassumption.
      by rewrite H'x'.
    - (* non-termination *)
      do 3 left. right. move=> b. apply: transition_loop => a' b' ??.
      move: Hx' H'x' => /multi_step'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] [Hz] /= [? ?].
      subst pz. exists (k'+1), az, bz.
      move: Hk' Hz => /multi_step'_incl /multi_step_plus -> /= ->.
      split; [done|lia]. }
  move: by' => [|by'] H'x'; first last.
  { (* case: (0, 1) f->>t-> (S a, S b) uniform transition to (S a, S b) *)
    right. move=> b. exists (k'+1).
    move: Hx' => /multi_step'E [n] [m] /= [Hax'] [Hbx'].
    move=> /(_ 0 (S b) ltac:(lia) ltac:(lia)) /multi_step'_incl.
    move: H'x' => /(step_parallel (state x', (n, S b + m))) /=.
    move=> /(_ ltac:(lia)).
    move=> [[pz' [az' bz']]] /= [Hz'] [? ?]. subst pz'.
    move=> Hx'. exists (az' - 1), (bz' - 1).
    move: Hx' Hz' => /multi_step_plus -> /= ->.
    congr Some. congr pair. congr pair; lia. }
  (* case: (0, 1) f->>t-> (S a, 0) *)
  have := multi_step'I (0, (1, 1)).
  move=> [k] [x] [Hx]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> b. move: Hx => /multi_step'_None_terminating.
    apply => /=; by [assumption|lia]. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 1) f->>t-> HALT; uniform termination *)
    move=> Hy. move: (Hx) (H'x) (Hy) => /terminating_orI => H /H {}H /H {H} [HS|?]; last by (do 4 left).
    do 4 left. move=> [|b].
    { move: HS => /(_ ay') [k'' ?]. exists (k' + (1 + k'')).
      move: Hx' => /multi_step'_incl /multi_step_plus ->.
      by move: H'x' => /(multi_step_plus 1) ->. }
    move: Hx' => /multi_step'E [n] [m] /= [?] [?].
    move=> /(_ 0 (S (S b)) ltac:(lia) ltac:(lia)).
    move: H'x' => /(step_parallel (state x', (n, S (S b) + m))) /=.
    move=> /(_ ltac:(lia)) [[pz' [az' bz']]] /=.
    move=> [Hz'] [?] ? Hx'.
    move: Hx => /multi_step'E [n'] [m'] /= [?] [?].
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
    move: Hx' => /multi_step'E [n] [m] /= [?] [?].
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
      move: Hx' => /multi_step'E [n] [m] /= [?] [?].
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
      move: Hx' H'x' => /multi_step'E [n] [m] /= [?] [?].
      move=> /(_ a' b' ltac:(lia) ltac:(lia)) Hk'.
      move=> /(step_parallel (state x', (a' + n, b' + m))) /=.
      move=> /(_ ltac:(lia)) [[pz [az bz]]] /= [Hz] [? ?]. subst pz.
      have [k'' Hk''] := H az bz.
      exists (k'+(1 + k'')), 0, (az * S b'y + bz).
      move: Hk' Hz Hk'' => /multi_step'_incl /multi_step_plus ->.
      move=> /(multi_step_plus 1) -> ->.
      split; first done. lia.
  - (* case: (1, 1) f->>t-> (S a', S b') loop *)
    do 3 left. right. move=> b. apply: dec_loop; [eassumption|].
    by rewrite H'x (config_eta y) H0y H1y H2y.
Qed.

(* uniform transition from equivalence class (S a, S b) *)
Lemma transition_Sa_Sb :
  (* terminating equivalence class (S a, 0) *)
  (forall a b, terminating (0, (S a, S b))) +
  (* non-terminating equivalence class (S a, 0) *)
  (forall a b, non_terminating (0, (S a, S b))) +
  (* uniform transition to equivalence class (0, 0) *)
  (forall a b, exists k, multi_step k (0, (S a, S b)) = Some (0, (0, 0))) +
  (* uniform transition to equivalence class (S a, 0) *)
  (forall a b, exists k a', multi_step k (0, (S a, S b)) = Some (0, (S a', 0))) +
  (* uniform transition to equivalence class (0, S b) *)
  (forall a b, exists k b', multi_step k (0, (S a, S b)) = Some (0, (0, S b'))).
Proof.
  have := multi_step'I (0, (1, 1)).
  move=> [k] [x] [Hk]. case H'x: (step x) => [y|]; first last.
  { (* case: (1, 1) f->> HALT; uniform termination *)
    move=> _. do 4 left. move=> a b.
    move: H'x Hk => /multi_step'_None_terminating H /H /=. apply; lia. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* case: (1, 0) f->>t-> HALT; uniform termination *)
    move: H'x Hk => /multi_step'_Some_terminating H /H {}H /H {}H.
    do 4 left. move=> a b. apply: H => /=; lia. }
  move: y H'x => [py' [[|ay'] [|by']]] H'x /= Hy'; subst py'.
  - (* case: (1, 1) f->>t-> (0, 0) impossible *)
    by move: Hk => /not_transition_1_1_to_0_0.
  - (* case: (1, 1) f->>t-> (0, S b) uniform transition to (0, S b) *)
    right. move=> a b.  
    move: Hk H'x => /dec_a_0 H /H /(_ (S a) (S b)) [k' Hk'].
    exists k', (S a * by' + S b - 1).
    rewrite Hk'. congr Some. congr pair. congr pair; lia.
  - (* case: (1, 1) f->>t-> (S a, 0) uniform transition to (S a, 0) *)
    do 1 left. right. move=> a b.  
    move: Hk H'x => /dec_b_0 H /H /(_ (S a) (S b)) [k' Hk'].
    exists k', (S b * ay' + S a - 1).
    rewrite Hk'. congr Some. congr pair. congr pair; lia.
  - (* case: (1, 1) f->>t-> (S a, S b) non-termination *)
    do 3 left. right. move=> a b.
    apply: dec_loop; by eassumption.
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

Lemma uniform_transition ab :
  In ab representatives -> 
  (* uniform termination *)
  (forall a'b', RZ ab a'b' -> terminating (0, a'b')) +
  (* uniform non-termination *)
  (forall a'b', RZ ab a'b' -> non_terminating (0, a'b')) +
  (* uniform transition *)
  {v | In v representatives /\
    (forall a'b', RZ ab a'b' -> exists k w, RZ v w /\ multi_step (S k) (0, a'b') = Some (0, w)) }.
Proof.
  rewrite /representatives /=.
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  case /HE; [|case /HE; [|case /HE; [|case /HE; last done]]] => <-.
  - have [[[[|]|]|]|] := transition_0_0.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia. done.
    + move=> H. right. exists (1, 0). split; first by tauto.
      move: H => [k] [a'' Hk].      
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (k-1), (S a'', 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (0, 1). split; first by tauto.
      move: H => [k] [b'' Hk].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (k-1), (0, S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (1, 1). split; first by tauto.
      move: H => [k] [a'' [b'' Hk]].
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = 0 by lia.
      exists (k-1), (S a'', S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
  - have [[[[|]|]|]|] := transition_Sa_0.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have [k Hk] := H (a'-1). exists (k-1), (0, 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (0, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have [k [b'' Hk]] := H (a'-1).
      exists (k-1), (0, S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (1, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = 0 by lia.
      have [k [a'' [b'' Hk]]] := H (a'-1).
      exists (k-1), (S a'', S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
  - have [[[[|]|]|]|] := transition_0_Sb.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have [k Hk] := H (b'-1). exists (k-1), (0, 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (1, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have [k [a'' Hk]] := H (b'-1).
      exists (k-1), (S a'', 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (1, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = 0 by lia. have ->: b' = S (b' - 1) by lia.
      have [k [a'' [b'' Hk]]] := H (b'-1).
      exists (k-1), (S a'', S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
  - have [[[[|]|]|]|] := transition_Sa_Sb.
    + move=> ?. left. left=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> ?. left. right=> - [a' b'] /= ?.
      have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia. done.
    + move=> H. right. exists (0, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have [k Hk] := H (a'-1) (b'-1). exists (k-1), (0, 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (1, 0). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have [k [a'' Hk]] := H (a'-1) (b'-1).
      exists (k-1), (S a'', 0). split; first by lia.
      by move: Hk => /multi_step_act <-.
    + move=> H. right. exists (0, 1). split; first by tauto.
      move=> [a' b'] /= ?. have ->: a' = S (a' - 1) by lia. have ->: b' = S (b' - 1) by lia.
      have [k [b'' Hk]] := H (a'-1) (b'-1).
      exists (k-1), (0, S b''). split; first by lia.
      by move: Hk => /multi_step_act <-.
Qed.

Opaque representatives.
Opaque CM2.multi_step.
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
    { w | In w L /\
      (forall ab, RZ v ab -> exists k a'b', RZ w a'b' /\ multi_step (S k) (0, ab) = Some (0, a'b')) } ) }.
  { exists representatives; first done. by apply: uniform_transition. }
  case. elim.
  { move=> _ H v /H /= [[|]|]; [tauto|tauto|].
    move=> {}H. exfalso. by case: H => ? []. }
  move=> v0 L IH /incl_cons_inv [Hv0 HL] HRZ. apply: IH; first done.
  move=> v /HRZ. move=> [[|]|]; [tauto|tauto|].
  have HE := @eq_or_inf (nat * nat) ltac:(by do ? decide equality).
  move=> [w] /= [/HE [|]]; first last.
  { move=> ??. right. by exists w. }
  move=> <-. move: Hv0 => /HRZ.
  move=> [[|]|].
  - (* termination *)
    move=> Hv0 Hv. left. left=> ab /Hv [k] [a'b'] [/Hv0].
    move=> [k' Hk'] HSk. exists ((S k) + k').
    by move: HSk => /multi_step_plus ->.
  - (* non-termination *)
    move=> Hv0 Hv. left. right=> ab /Hv [k] [a'b'] [/Hv0].
    move=> Ha'b' HSk k'.
    move=> /(multi_step_k_monotone ((S k)+k')) /(_ ltac:(lia)).
    move: HSk => /multi_step_plus ->. by apply: Ha'b'.
  - (* chaining *)
    move=> [w'] /= [/HE [|]].
    + (* non-termination *)
      move=> <- /RZ_loop Hv0 Hv. left. right=> ab /Hv [k] [a'b'] [/Hv0].
      move=> Ha'b' HSk k'.
      move=> /(multi_step_k_monotone ((S k)+k')) /(_ ltac:(lia)).
      move: HSk => /multi_step_plus ->. by apply: Ha'b'.
    + move=> ? Hv0 Hv. right. exists w'. split; first done.
      move=> ab /Hv [k] [a'b'] [/Hv0] [k'] [a''b''] [? HSk'] HSk.
      exists (k + (S k')), a''b''. split; first done.
      have ->: S (k + S k') = (S k) + (S k') by done.
      by move: HSk => / multi_step_plus ->.
Qed.

Lemma uniform_decision_0 a b : (terminating (0, (a, b))) + (non_terminating (0, (a, b))).
Proof.
  have [v []] := get_representative (a, b).
  move=> /uniform_representative_decision [] => H /H; tauto.
Qed.

Lemma uniform_decision (c: Config) : (terminating c) + (non_terminating c).
Proof.
  have := multi_step'I c.
  move=> [k] [y] [Hk].
  case Hz: (step y) => [[pz [az bz]]|] /=; first last.
  { (* termination *)
    move=> _. left. exists (k+1).
    by move: Hk => /multi_step'_incl /multi_step_plus ->. }
  case /(eq_or_inf Nat.eq_dec); first last.
  { (* termination *)
    move=> /nth_error_None Hpz. left.
    exists (k+(1+1)).
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    move: Hz => /(multi_step_plus 1) ->.
    have -> : multi_step 1 = step by done.
    by rewrite /step Hpz. }
  move=> ?. subst pz.
  case: (uniform_decision_0 az bz).
  - (* termination *)
    move=> + /ltac:(left). move=> [k' Hk']. exists (k+(1+k')).
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    by move: Hz => /(multi_step_plus 1) ->.
  - (* non-termination *)
    move=> H'z. right=> k'.
    move=> /(multi_step_k_monotone (k+(1+k'))) /(_ ltac:(lia)).
    move: Hk => /multi_step'_incl /multi_step_plus ->.
    move: Hz => /(multi_step_plus 1) ->. apply: H'z.
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
