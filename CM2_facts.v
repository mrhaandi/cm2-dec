Require Import List Lia PeanoNat.
Import ListNotations.

Require Import M2.CM2.

Require Import ssreflect ssrbool ssrfun.

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma iter_None {X : Type} (f : X -> option X) k : Nat.iter k (option_bind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

Lemma option_bind_iter {X : Type} (f : X -> option X) k x : 
  option_bind f (Nat.iter k (option_bind f) (Some x)) = Nat.iter k (option_bind f) (f x).
Proof. elim: k; [done|by move=> k /= ->]. Qed.

Section Dup.

Context {X : Type} (X_eq_dec : forall (x y : X), {x = y} + {x <> y}).

Lemma pigeonhole (L L' : list X) : incl L L' -> length L' < length L -> not (NoDup L).
Proof.
  move=> ++ HL. elim: HL L'.
  { move=> /=. lia. }
  move=> x {}L HxL HL IH L' /(@incl_cons_inv X) [/(@remove_length_lt X X_eq_dec) HxL' HLL'].
  move: HLL' => /(@remove_incl X X_eq_dec L L' x).
  rewrite notin_remove /=; first done.
  move=> /IH. lia.
Qed.

Lemma not_inclE (L L' : list X) : (not (incl L L')) -> { x | In x L /\ not (In x L')}.
Proof.
  elim: L. { move=> H. exfalso. by apply: H. }
  move=> x L IH /=.
  have [|?] := In_dec X_eq_dec x L'.
  - move=> ? HxLL'. have /IH [y [? ?]] : ~ incl L L'.
    { move=> H. apply: HxLL'. by move=> y /= [<-|/H]. }
    exists y. tauto.
  - move=> _. exists x. tauto.
Qed.

(* TODO part of Coq stdlib ListDec *)
Lemma NoDup_dec (L : list X) : {NoDup L} + {not (NoDup L)}.
Proof.
  elim: L.
  {left. by constructor. }
  move=> x L [IH|IH].
  - have [HxL|HxL] := In_dec X_eq_dec x L.
    + right. move=> /NoDup_cons_iff. tauto.
    + left. by constructor.
  - right. by move=> /NoDup_cons_iff [_ /IH].
Qed.

(* explicit duplicates in a mapped sequence *)
Lemma dup_seq (f : nat -> X) start len :
  not (NoDup (map f (seq start len))) ->
  exists '(i, j), f i = f j /\ (start <= i /\ i < j /\ j < start+len).
Proof.
  elim: len start.
  { move=> start /= H. exfalso. apply: H. by constructor. }
  move=> len IH start /=.
  have [|] := NoDup_dec (map f (seq (S start) len)).
  - move=> H1f H2f. have : In (f start) (map f (seq (S start) len)).
    { have [|] := In_dec X_eq_dec (f start) (map f (seq (S start) len)); first done.
      by move: H1f => /(@NoDup_cons X) H /H /H2f. }
    move=> /in_map_iff [j] [?] /in_seq ?. exists (start, j).
    split; first done. lia.
  - move=> /IH [[i j]] [? ?] _.
    exists (i, j). split; first done. lia.
Qed.

End Dup.

Definition reaches_plus (M: Cm2) (x y: Config) := exists k, 0 < k /\ multi_step M k x = Some y.
Definition non_terminating (M: Cm2) (x: Config) := forall k, multi_step M k x <> None.

Section Facts.
Context {M : Cm2}.

Notation step := (CM2.step M).
Notation multi_step := (CM2.multi_step M).
Notation reaches := (CM2.reaches M).
Notation reaches_plus := (reaches_plus M).
Notation terminating := (CM2.terminating M).
Notation non_terminating := (non_terminating M).

Lemma multi_step_k_monotone {k x} k' : multi_step k x = None -> k <= k' -> multi_step k' x = None.
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

Lemma multi_step_plus {k x k' y} :
  multi_step k x = Some y -> multi_step (k + k') x = multi_step k' y.
Proof. rewrite /multi_step iter_plus. by move=> ->. Qed.

Lemma step_None x : step x = None <-> nth_error M (state x) = None.
Proof.
  rewrite /step. case: (nth_error M (state x)) => [i|]; last done.
  case: i; first done.
  by move: (value1 x) (value2 x) => [|?] [|?] [].
Qed.

Lemma reaches_plus_reaches {x y z} : reaches_plus x y -> reaches y z -> reaches_plus x z.
Proof.
  move=> [k [? Hk]] [k' Hk']. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /multi_step iter_plus => ->.
Qed.

Lemma reaches_reaches_plus {x y z} : reaches x y -> reaches_plus y z -> reaches_plus x z.
Proof.
  move=> [k Hk] [k' [? Hk']]. exists (k+k'). split; first by lia.
  move: Hk. by rewrite /multi_step iter_plus => ->.
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
  move: Hk. by rewrite /multi_step iter_plus => ->.
Qed.

Lemma reaches_non_terminating {x y} : reaches x y -> non_terminating y -> non_terminating x.
Proof.
  move=> [k Hk] Hy k'.
  have [|->] : k' <= k \/ k' = k + (k' - k) by lia.
  - by move: Hk => + /multi_step_k_monotone H /H => ->.
  - rewrite (multi_step_plus Hk). by apply: Hy.
Qed.

Lemma reaches_non_terminating' {x y} : reaches x y -> non_terminating x -> non_terminating y.
Proof.
  move=> [k' Hk'] Hx k Hk.
  apply: (Hx (k' + k)).
  by rewrite (multi_step_plus Hk').
Qed.

Lemma reaches_plus_state_bound {x y} : reaches_plus x y -> state x < length M.
Proof.
  move=> [k [? Hk]].
  suff: not (length M <= state x) by lia.
  move=> /nth_error_None Hx.
  move: Hk. have ->: k = S (k - 1) by lia.
  by rewrite /= option_bind_iter /step Hx iter_None.
Qed.

Lemma reaches_plus_trans {x y z} : reaches_plus x y -> reaches_plus y z -> reaches_plus x z.
Proof. by move=> /reaches_plus_incl /reaches_reaches_plus H /H. Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. move=> [k Hk] [k' Hk']. exists (k+k'). by rewrite (multi_step_plus Hk). Qed.

Lemma reaches_plus_invariant_loop (P : Config -> Prop) :
  (forall x, P x -> exists y, reaches_plus x y /\ P y) ->
  forall x, P x -> non_terminating x.
Proof.
  move=> H x Hx k. elim: k x Hx; first done.
  move=> k IH x /H [y] [[k' [? Hk']]] /IH Hk.
  move=> /(multi_step_k_monotone (k' + k)) /(_ ltac:(lia)).
  by rewrite (multi_step_plus Hk').
Qed.

Corollary reaches_plus_self_loop x : reaches_plus x x -> non_terminating x.
Proof.
  move=> ?. apply: (reaches_plus_invariant_loop (fun y => y = x)); last done.
  move=> y ->. by exists x. 
Qed.

End Facts.

(*
Require Import M2.Nat_facts.

Require Import ssreflect.

Set Default Goal Selector "!".

Lemma haltingP {cm c} : halting cm c <-> length cm <= state c.
Proof.
  move:c => [p a b]. rewrite /halting /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by move=> /nth_error_None.
  move=> [] x => [|?] Hp /=.
  - constructor; [by case; lia | by rewrite -nth_error_None Hp].
  - move: x a b Hp => [] [|?] [|?]; 
      (constructor; [by case; lia | by rewrite -nth_error_None Hp]).
Qed.

Lemma halting_eq {cm c n} : halting cm c -> Nat.iter n (step cm) c = c.
Proof.
  move=> Hc. elim: n; first done.
  move=> ? /= ->. by rewrite Hc.
Qed.

(* halting is monotone *)
Lemma halting_monotone {cm x} (n m: nat) : n <= m ->
  halting cm (Nat.iter n (step cm) x) -> halting cm (Nat.iter m (step cm) x).
Proof.
  move=> ? ?. have -> : m = n + (m-n) by lia.
  rewrite iter_plus. elim: (m-n); [done | by move=> * /=; congruence].
Qed.

Lemma values_ub cm c n : 
  value1 (Nat.iter n (CM2.step cm) c) + value2 (Nat.iter n (CM2.step cm) c) <= n + value1 c + value2 c.
Proof.
  move Hk : (n + value1 c + value2 c) => k.
  have : n + value1 c + value2 c <= k by lia.
  elim: n k c {Hk}; first done.
  move=> n IH k [p a b]. rewrite -/(1 + n) iter_plus /=. 
  case: (nth_error cm p).
  - move=> [] [] => [||?|?]; move: a b => [|?] [|?] /= ?; apply: IH => /=; by lia.
  - move=> ?. apply: IH => /=. by lia.
Qed.
*)
