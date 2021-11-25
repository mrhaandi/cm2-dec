(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Decision procedure for two-counter Minsky machine halting
*)

Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import M2.Facts M2.MM2.

Section Construction.
Variable M : Mm2.

#[local] Notation step := (MM2.step M).
#[local] Notation steps := (MM2.steps M).
#[local] Notation terminating := (MM2.terminating M).
#[local] Notation l := (length M).

(* after k steps values change at most by k (or are reset and at most k) *)
Lemma steps_bound {k p a b p' a' b'} : steps k (p, (a, b)) = Some (p', (a', b')) -> 
  a' <= k + a /\ b' <= k + b /\ (a' <= k \/ a <= k + a') /\ (b' <= k \/ b <= k + b').
Proof.
  elim: k p' a' b'.
  { move=> p' a' b' /= []. lia. }
  move=> k + p' a' b' /=.
  case: (steps k (p, (a, b))) => [[p'' [a'' b'']]|]; last done.
  move=> /(_ p'' a'' b'' ltac:(done)) IH.
  rewrite /= /(step _).
  case: (nth_error M (state (p'', (a'', b'')))); last done.
  case.
  - done.
  - case; case; lia.
  - case; case; lia.
  - case => q /=.
    + move: b'' IH => [|b''] ? []; lia.
    + move: a'' IH => [|a''] ? []; lia.
Qed.

Definition reaches (x y: Config) := exists k, steps k x = Some y.
Definition reaches_plus (x y: Config) := exists k, 0 < k /\ steps k x = Some y.
Definition non_terminating x := forall k, steps k x <> None.

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

Lemma reaches_terminating {x y} : reaches x y -> terminating y -> terminating x.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k').
  move: Hk. by rewrite /steps iter_plus => ->.
Qed.

Lemma steps_k_monotone {k x} k' : steps k x = None -> k <= k' -> steps k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
Qed.

Lemma steps_plus {k x k' y} :
steps k x = Some y -> steps (k + k') x = steps k' y.
Proof. rewrite /steps iter_plus. by move=> ->. Qed.

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

Lemma reaches_plus_state_bound {x y} : reaches_plus x y -> state x < l.
Proof.
  move=> [k [? Hk]].
  suff: not (l <= state x) by lia.
  move=> /nth_error_None Hx.
  move: Hk. have ->: k = S (k - 1) by lia.
  by rewrite /= obind_oiter /step Hx oiter_None.
Qed.

Lemma reaches_plus_trans {x y z} : reaches_plus x y -> reaches_plus y z -> reaches_plus x z.
Proof. by move=> /reaches_plus_incl /reaches_reaches_plus H /H. Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. move=> [k Hk] [k' Hk']. exists (k+k'). by rewrite (steps_plus Hk). Qed.

(* a configuration (p, (a, b))
  is either halting or uniformly transitions into a configuration with one zero counter *)
Lemma next_waypoint p a b :
  terminating (p, (a, b)) +
  { '(p', a') | forall n, exists k, 0 < k <= l - p /\ steps k (p, (n+a, b)) = Some (p', (n+a', 0)) } +
  { '(p', b') | forall n, exists k, 0 < k <= l - p /\ steps k (p, (a, n+b)) = Some (p', (0, n+b')) }.
Proof.
  move Hn: (l - p) => n. elim: n p Hn a b.
  { move=> p ? a b. left. left. exists 1. rewrite /= /step.
    by have ->: nth_error M (state (p, (a, b))) = None
      by (rewrite nth_error_None /=; lia). }
  move=> n IH p ? a b.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; first last.
  { left. left. exists 1. by rewrite /= /step Hi. }
  move: i Hi => /= [].
  - move=> Hi. left. left. exists 1. by rewrite /= /step Hi.
  - case.
    + move=> Hi. left. right. exists (S p, a).
      move=> n'. exists 1. split; first by lia.
      by rewrite /= /step /= Hi.
    + move=> Hi. right. exists (S p, b).
      move=> n'. exists 1. split; first by lia.
      by rewrite /= /step /= Hi.
  - case.
    + move=> Hi.
      have [[|[[p' a'] HSp]]|[[p' b'] HSp]] := IH (S p) ltac:(lia) a (S b).
      * move=> /reaches_terminating HSp. left. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * left. right. exists (p', a').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi Nat.add_succ_r.
    + move=> Hi.
      have [[|[[p' a'] HSp]]|[[p' b'] HSp]] := IH (S p) ltac:(lia) (S a) b.
      * move=> /reaches_terminating HSp. left. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * left. right. exists (p', a').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi Nat.add_succ_r.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi.
  - case=> q Hi.
    + move: b => [|b].
      { left. right. exists (q, a) => n'. exists 1. 
        split; first by lia. by rewrite /= /step Hi. }
      have [[|[[p' a'] HSp]]|[[p' b'] HSp]] := IH (S p) ltac:(lia) a b.
      * move=> /reaches_terminating HSp. left. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * left. right. exists (p', a').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi Nat.add_succ_r.
    + move: a => [|a].
      { right. exists (q, b) => n'. exists 1. 
        split; first by lia. by rewrite /= /step Hi. }
      have [[|[[p' a'] HSp]]|[[p' b'] HSp]] := IH (S p) ltac:(lia) a b.
      * move=> /reaches_terminating HSp. left. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * left. right. exists (p', a').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi Nat.add_succ_r.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: steps_plus. by rewrite /= /step Hi.
Qed.

(* terminate or reach uniformly next config or reach small config *)
Corollary next_waypoint_a p a :
  terminating (p, (a, 0)) +
  { '(p', a') | forall n, reaches_plus (p, (n+a, 0)) (p', (n+a', 0)) } +
  { '(p', (a', b')) | reaches (p, (a, 0)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  have [[?|[[p' a'] Hp]]|[[p' b'] Hp]] := next_waypoint p a 0.
  - left. by left.
  - left. right. exists (p', a') => n.
    have [k [? Hk]] := Hp n. exists k.
    split; [lia|done].
  - right. exists (p', (0, b')).
    have [k [? Hk]] := Hp 0.
    have ? := steps_bound Hk.
    split; [by exists k|lia].
Qed.

(* terminate or reach uniformly next config or reach small config *)
Corollary next_waypoint_b p b :
  terminating (p, (0, b)) +
  { '(p', b') | forall n, reaches_plus (p, (0, n+b)) (p', (0, n+b')) } +
  { '(p', (a', b')) | reaches (p, (0, b)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  have [[?|[[p' a'] Hp]]|[[p' b'] Hp]] := next_waypoint p 0 b.
  - left. by left.
  - right. exists (p', (a', 0)).
    have [k [? Hk]] := Hp 0.
    have ? := steps_bound Hk.
    split; [by exists k|lia].
  - left. right. exists (p', b') => n.
    have [k [? Hk]] := Hp n. exists k.
    split; [lia|done].
Qed.

Lemma loop_a {p a a' b} :
  a <= a' ->
  (forall n : nat, reaches_plus (p, (n + a, b)) (p, (n + a', b))) ->
  non_terminating (p, (a, b)).
Proof.
  move=> ? Hp k.
  suff: forall m, steps k (p, (m + a, b)) <> None by move=> /(_ 0).
  elim: k; first done.
  move=> k IH m.
  have [k' [? Hk']] := Hp m.
  move=> /(steps_k_monotone (k' + k)) /(_ ltac:(lia)).
  move: Hk' => /steps_plus ->.
  have ->: m + a' = (m + a' - a) + a by lia.
  by apply: IH.
Qed.

Lemma loop_b {p a b b'} :
  b <= b' ->
  (forall n : nat, reaches_plus (p, (a, n + b)) (p, (a, n + b'))) ->
  non_terminating (p, (a, b)).
Proof.
  move=> ? Hp k.
  suff: forall m, steps k (p, (a, m + b)) <> None by move=> /(_ 0).
  elim: k; first done.
  move=> k IH m.
  have [k' [? Hk']] := Hp m.
  move=> /(steps_k_monotone (k' + k)) /(_ ltac:(lia)).
  move: Hk' => /steps_plus ->.
  have ->: m + b' = (m + b' - b) + b by lia.
  by apply: IH.
Qed.

Lemma reaches_plus_self_loop x : reaches_plus x x -> non_terminating x.
Proof.
  move=> [k [? Hk]]. elim; first done.
  move=> k' Hk'.
  move=> /(steps_k_monotone (k + k')) /(_ ltac:(lia)).
  by rewrite (steps_plus Hk).
Qed.

Definition update {X : Type} (f : nat -> X) n x :=
  fun m => if Nat.eq_dec m n is left _ then x else f m.

Inductive R : (nat -> option nat) -> (nat -> option nat) -> Prop :=
  | R_None f p c : p < l -> f p = None -> R (update f p (Some c)) f
  | R_Some c' f p c : p < l -> f p = Some c' -> c < c' -> R (update f p (Some c)) f.

Lemma wf_R : well_founded R.
Proof.
  pose F := (fun (f : nat -> option nat) => 
    list_sum (map (fun p => if f p is None then 1 else 0) (seq 0 l))).
  pose G := (fun (f : nat -> option nat) => 
    list_sum (map (fun p => if f p is Some c then c else 0) (seq 0 l))).
  elim /(measure_ind F). elim /(measure_ind G).
  move=> f IHG IHF. constructor => g Hgf.
  case: Hgf IHG IHF.
  - move=> {}f p c ? Hf IHG IHF.
    apply: IHF. rewrite /F.
    have /list_sum_map_lt : In p (seq 0 l) by (apply /in_seq; lia).
    apply.
    + move=> p''. case Hp'': (f p'') => [c''|].
      * rewrite /update Hp''. by case: (Nat.eq_dec p'' p).
      * rewrite /update Hp''. case: (Nat.eq_dec p'' p); lia.
    + rewrite /update Hf. case: (Nat.eq_dec p p); lia.
  - move=> c' {}f p c Hl Hf ? IHG IHF.
    apply: IHG; first last.
    { move=> h Hh. apply: IHF.
      suff: F (update f p (Some c)) <= F f by lia.
      apply: list_sum_map_le.
      move=> p''. case Hp'': (f p'') => [c''|].
      - rewrite /update Hp''. by case: (Nat.eq_dec p'' p).
      - rewrite /update Hp''. case: (Nat.eq_dec p'' p); lia. }
    rewrite /G.
    have : In p (seq 0 l) by (apply /in_seq; lia).
    move=> /list_sum_map_lt. apply.
    + move=> p''. case Hp'': (f p'') => [c''|].
      * rewrite /update. case: (Nat.eq_dec p'' p).
        ** move=> ?. subst. move: Hf Hp'' => -> []. lia.
        ** rewrite Hp''. lia.
      * rewrite /update. case: (Nat.eq_dec p'' p).
        ** move=> ?. subst. by move: Hf Hp'' => ->.
        ** rewrite Hp''. lia.
    + rewrite /update Hf. by case: (Nat.eq_dec p p).
Qed.

Lemma big_wf_a p a (f : nat -> option nat) :
  (forall p' a', f p' = Some a' -> forall n, reaches_plus (p', (n+a', 0)) (p, (n+a, 0))) ->
  terminating (p, (a, 0)) +
  non_terminating (p, (a, 0)) +
  { '(p', (a', b')) | reaches (p, (a, 0)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  elim /(well_founded_induction_type wf_R) : f p a.
  move=> f IH p a Hf.
  have [[Hp|[[p' a'] Hp]]|[[p' [a' b']] [Hp ?]]] := next_waypoint_a p a.
  - left. by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    set P := (_ + _ + _)%type.
    have HR : R (update f p (Some a)) f -> P.
    { move=> /IH /(_ p' a') /=. case; [|case|].
      - move=> p''' a'''. rewrite /update.
        case: (Nat.eq_dec p''' p).
        { by move=> -> [<-]. }
        move=> ? /Hf Hp''' n.
        by apply: (reaches_plus_trans (Hp''' n) (Hp n)).
      - move=> /reaches_terminating Hp'. left. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      - move=> /reaches_non_terminating Hp'. left. right.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      - move=> [[p''' [a''' b''']]] [Hp'] ?. right.
        exists (p''', (a''', b''')). split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))). }
    case H'p: (f p) => [a''|].
    + case E: (a''-a) => [|?].
      { left. right. move: H'p => /Hf{Hf} H'p.
        apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
        apply: (loop_a _ H'p). lia. }
      apply /HR /(R_Some a''); [done|done|lia].
    + by apply /HR /R_None.
  - right. by exists (p', (a', b')).
Qed.


Lemma big_wf_b p b (f : nat -> option nat) :
  (forall p' b', f p' = Some b' -> forall n, reaches_plus (p', (0, n+b')) (p, (0, n+b))) -> 
  terminating (p, (0, b)) +
  non_terminating (p, (0, b)) +
  { '(p', (a', b')) | reaches (p, (0, b)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  elim /(well_founded_induction_type wf_R) : f p b.
  move=> f IH p b Hf.
  have [[Hp|[[p' b'] Hp]]|[[p' [a' b']] [Hp ?]]] := next_waypoint_b p b.
  - left. by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    set P := (_ + _ + _)%type.
    have HR : R (update f p (Some b)) f -> P.
    { move=> /IH /(_ p' b') /=. case; [|case|].
      - move=> p''' b'''. rewrite /update.
        case: (Nat.eq_dec p''' p).
        { by move=> -> [<-]. }
        move=> ? /Hf Hp''' n.
        by apply: (reaches_plus_trans (Hp''' n) (Hp n)).
      - move=> /reaches_terminating Hp'. left. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      - move=> /reaches_non_terminating Hp'. left. right.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      - move=> [[p''' [a''' b''']]] [Hp'] ?. right.
        exists (p''', (a''', b''')). split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))). }
    case H'p: (f p) => [b''|].
    + case E: (b''-b) => [|?].
      { left. right. move: H'p => /Hf{Hf} H'p.
        apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
        apply: (loop_b _ H'p). lia. }
      apply /HR /(R_Some b''); [done|done|lia].
    + by apply /HR /R_None.
  - right. by exists (p', (a', b')).
Qed.

(* from any config can decide termination or get to next small waypoint *)
Lemma next_small_waypoint p a b :
  terminating (p, (a, b)) +
  non_terminating (p, (a, b)) +
  { '(p', (a', b')) | reaches_plus (p, (a, b)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  have [[?|[[p' a'] Hp]]|[[p' b'] Hp]] := next_waypoint p a b.
  - left. by left.
  - have [[|]|] := big_wf_a p' a' (fun _ => None) ltac:(done).
    * move=> /reaches_terminating Hp'. left. left.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> /reaches_non_terminating Hp'. left. right.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> [[p'' [a'' b'']]] [Hp'] ?. right.
      exists (p'', (a'', b'')). split; last done.
      apply: (reaches_plus_reaches _ Hp').
      have [k [? Hk]] := Hp 0. exists k. split; [lia|done].
  - have [[|]|] := big_wf_b p' b' (fun _ => None) ltac:(done).
    * move=> /reaches_terminating Hp'. left. left.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> /reaches_non_terminating Hp'. left. right.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> [[p'' [a'' b'']]] [Hp'] ?. right.
      exists (p'', (a'', b'')). split; last done.
      apply: (reaches_plus_reaches _ Hp').
      have [k [? Hk]] := Hp 0. exists k. split; [lia|done].
Qed.

Lemma small_decider p a b L : a <= l -> b <= l ->
  Forall (fun '(p', (a', b')) => reaches_plus (p', (a', b')) (p, (a, b)) /\ p' < l /\ a' <= l /\ b' <= l ) L ->
  NoDup L ->
  terminating (p, (a, b)) + non_terminating (p, (a, b)).
Proof.
  move Hn: ((l*(l+1)*(l+1)+1) - length L) => n.
  elim: n L Hn p a b.
  { move=> L ? ????? H1L /NoDup_incl_length H2L.
    have : incl L (list_prod (seq 0 l) (list_prod (seq 0 (l+1)) (seq 0 (l+1)))).
    { move=> [p [a b]].
      move: H1L => /Forall_forall H1L /H1L ?.
      apply /in_prod; [|apply /in_prod]; apply /in_seq; lia. }
    move=> /H2L. rewrite ?prod_length ?seq_length. lia. }
  move=> n IH L ? p a b ? ? H1L H2L.
  have [[|]|[[p' [a' b']] [Hp ?]]] := next_small_waypoint p a b; [tauto|tauto|].
  have := In_dec _ (p, (a, b)) L. case.
  { do ? decide equality. }
  - move=> H'p. right. apply: reaches_plus_self_loop.
    by move: H1L H'p => /Forall_forall H /H [].
  - move=> H'p. 
    have := (IH ((p, (a, b)) :: L) _ p' a' b'). case.
    + move=> /=. lia.
    + lia.
    + lia.
    + constructor.
      * split; first done.
        move: Hp => /reaches_plus_state_bound /=. lia.
      * apply: Forall_impl H1L.
        move=> [p'' [a'' b'']] [? ?]. split; last done.
        by apply: (reaches_plus_reaches _ (reaches_plus_incl Hp)).
    + by constructor.
    + move=> /reaches_terminating H. left. by apply /H /reaches_plus_incl.
    + move=> /reaches_non_terminating H. right. by apply /H /reaches_plus_incl.
Qed.

Lemma uniform_decision x : terminating x + non_terminating x.
Proof.
  move: x => [p [a b]].
  have [[|]|] := next_small_waypoint p a b; [tauto|tauto|].
  move=> [[p' [a' b']]] [/reaches_plus_incl Hp'] [Ha' Hb'].
  have := small_decider p' a' b' [] Ha' Hb' ltac:(by constructor) ltac:(by constructor).
  case.
  - move: Hp' => /reaches_terminating H /H ?. by left.
  - move: Hp' => /reaches_non_terminating H /H ?. by right.
Qed.

End Construction.

(* decision procedure for the halting problem for Mm2 *)
Definition decider (M: Mm2) (c: Config) : bool :=
  match uniform_decision M c with
  | inl _ => true
  | inr _ => false
  end.

(* decision procedure correctness *)
Lemma decider_spec (M: Mm2) (c: Config) :
  (terminating M c) <-> (decider M c = true).
Proof.
  rewrite /decider. case: (uniform_decision M c).
  - tauto.
  - move=> H. split; [by move=> [k /H] | done].
Qed.
