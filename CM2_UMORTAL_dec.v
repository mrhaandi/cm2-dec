Require Import List PeanoNat Lia Operators_Properties ConstructiveEpsilon.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.
Require Import M2.CM2 M2.CM2_facts.
Require M2.CM2_UBOUNDED_dec.

Section BoundConstruction.

Variable M : Cm2.

Notation bounded := (bounded M).

(* uniform bound *)
Variable K : nat.
Variable HK : forall x, bounded K x.

Notation step := (CM2.step M).
Notation multi_step := (CM2.multi_step M).
Notation mortal := (CM2.mortal M).

Lemma bounded_inf k x : bounded k x -> {L | (length L <= k) /\ (forall (y: Config), reaches M x y -> In y L) }.
Proof.
  move=> Hkx. exists (map (fun n => if multi_step n x is Some y then y else x) (seq 0 k)).
  split; first by rewrite map_length seq_length.
  move=> y Hxy. admit. (* hard, doable *)
Admitted.

Lemma pointwise_decision k x : (mortal k x) + (not (mortal k x)).
Proof. rewrite /mortal. by case: (multi_step k x) => [y|]; [right|left]. Qed.

Lemma pigeonhole {X : Type} (L L' : list X) : incl L L' -> length L' < length L -> not (NoDup L).
Proof. Admitted.

Lemma dup_seq {X : Type} (f : nat -> X) start len :
  not (NoDup (map f (seq start len))) ->
  exists '(i, j), f i = f j /\ (start <= i /\ i < j /\ j <= start+len).
Proof.
  elim: len start.
  { move=> start /= H. exfalso. apply: H. by constructor. }
  move=> len IH start /=.
Admitted. 

Lemma mortal_bound k x : mortal k x -> mortal K x.
Proof.
  rewrite /mortal. have [HkK|HKk] : k <= K \/ K < k by lia.
  { move=> /multi_step_k_monotone. by apply. }
  case Hxy: (multi_step K x) => [y|]; last done.
  have [L [? HL]] := HK x.
  have : incl (map (fun n => if multi_step n x is Some y then y else x) (seq 0 (K+1))) L.
  { move=> z /in_map_iff [k'] [+ /in_seq ?].
    case Hk': (multi_step k' x) => [z'|]; first last.
    { move: Hk' => /(multi_step_k_monotone K) /(_ ltac:(lia)).
      by rewrite Hxy. }
    move=> <-. apply: HL. by exists k'. }
  move=> /pigeonhole. rewrite map_length seq_length.
  move=> /(_ ltac:(lia)) /dup_seq [[k1 k2]] [+ ?].
  case Hk1: (multi_step k1 x) => [z|]; first last.
  { admit. (* easy *) }
  case Hk2: (multi_step k2 x) => [z'|]; first last.
  { admit. (* easy *) }
  move=> ?. subst z'.
  admit. (* doable *)
Admitted.

Lemma pos_K : K = 1 + (K - 1).
Proof.
  suff: K <> 0 by lia.
  move=> H'K.
  have := HK (0, (0, 0)). rewrite H'K.
  move=> [[|L]].
  - by move=> [_] /(_ (0, (0, 0)) (reaches_refl _)).
  - move=> ? /=. lia.
Qed.

Lemma mortal_K_bound_a {p a b} :
  K <= a -> mortal K (p, (a, b)) <-> mortal K (p, (K, b)).
Proof.
  rewrite /(mortal _). elim: (K) p a b; first done.
  move=> K' IH p a b Ha.
  rewrite /= ?option_bind_iter /step -/step /=.
  case: (nth_error M p) => [i|]; last done.
  case: i.
  - move=> c. rewrite -?/(multi_step _ _).
    rewrite (IH _ (_ + a) (_ + b) ltac:(lia)).
    by rewrite (IH _ (_ + (S K')) (_ + b) ltac:(lia)).
  - move=> [] q.
    + case: b => [|b].
      * rewrite -?/(multi_step _ _).
        rewrite (IH _ a 0 ltac:(lia)).
        by rewrite (IH _ (S K') 0 ltac:(lia)).
      * rewrite -?/(multi_step _ _).
        rewrite (IH _ a b ltac:(lia)).
        by rewrite (IH _ (S K') b ltac:(lia)).
    + case: a Ha => [|a] Ha; first by lia.
      rewrite -?/(multi_step _ _).
      apply: IH. lia.
Qed.

Lemma mortal_K_bound_b {p a b} :
  K <= b -> mortal K (p, (a, b)) <-> mortal K (p, (a, K)).
Proof.
Admitted.

Lemma uniform_decision : (uniformly_mortal M) + (not (uniformly_mortal M)).
Proof.
  have := Forall_dec (fun 'x => mortal K x) _
    (list_prod (seq 0 (length M)) (list_prod (seq 0 (K+1)) (seq 0 (K+1)))).
  case.
  { move=> x. rewrite /(mortal K). by case: (multi_step K x) => [y|]; [right|left]. }
  - move=> H'M. left. exists K => - [p [a b]].
    have [?|?] : length M <= p \/ p < length M by lia.
    { rewrite /(mortal K) pos_K /multi_step iter_plus /= /step /=.
      have -> : nth_error M p = None by apply /nth_error_None.
      by rewrite iter_None. }
    wlog ? : a /(a <= K).
    { move=> H. (have [?|/mortal_K_bound_a] : a <= K \/ K <= a by lia); first by apply H.
      move=> ->. by apply: H. }
    wlog ? : b /(b <= K).
    { move=> H. (have [?|/mortal_K_bound_b] : b <= K \/ K <= b by lia); first by apply H.
      move=> ->. by apply: H. }
    move: H'M => /Forall_forall. apply.
    apply /in_prod.
    { apply /in_seq. lia. }
    apply /in_prod; apply /in_seq; lia.
  - move=> H. right => - [K' H'M]. apply: H. apply /Forall_forall.
    move=> [p [a b]] /in_prod_iff [/in_seq ?] /in_prod_iff [/in_seq ?] /in_seq ?.
    by apply /mortal_bound /H'M.
Qed.
End BoundConstruction.



Section BoundRefutation.

Variable M : Cm2.
Variable HM : not (uniformly_bounded M).

Notation multi_step := (CM2.multi_step M).

(* an unbounded machine is immortal *)
Lemma not_uniformly_mortal : not (uniformly_mortal M).
Proof.
  move=> [k Hk]. apply: HM. exists k => x.
  exists (map (fun n => if multi_step n x is Some y then y else x) (seq 0 k)).
  split.
  { rewrite map_length seq_length. lia. }
  move=> y [k' Hk'].
  have [?|?] : k' < k \/ k <= k' by lia.
  - apply /in_map_iff. exists k'. rewrite Hk'.
    split; first done. apply /in_seq. lia.
  - have := Hk x. rewrite /mortal.
    move=> /(multi_step_k_monotone k') /(_ ltac:(lia)).
    by rewrite Hk'.
Qed.

End BoundRefutation.

(* informative decision statement for uniform boundedness for Cm2 *)
Theorem decision (M: Cm2) : (uniformly_mortal M) + (not (uniformly_mortal M)).
Proof.
  case: (CM2_UBOUNDED_dec.decision M).
  - move=> /constructive_indefinite_ground_description.
    move=> /(_ id id ltac:(done) (CM2_UBOUNDED_dec.fixed_decision M)).
    by move=> [K /uniform_decision].
  - move=> H. right. by apply: not_uniformly_mortal.
Qed.

(* boolean decision procedure for uniform mortality for Cm2 *)
Definition decider (M: Cm2) : bool :=
  match decision M with
  | inl _ => true
  | inr _ => false
  end.

(* decision procedure correctness *)
Lemma decider_spec (M: Cm2) :
  (uniformly_mortal M) <-> (decider M = true).
Proof.
  rewrite /decider. case: (decision M); intuition done.
Qed.

Print Assumptions decider.

(* BoundConstruction decides uniform mortality knowing uniform bound
BoundRefutation refutes uniform mortality with no uniform bound *)
