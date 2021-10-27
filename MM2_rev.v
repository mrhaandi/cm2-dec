(* decider for MM2 halting *)

Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect.
Require Import CM2.MM2.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

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

Section ForallNorm.
Context {X : Type} {P : X -> Prop}.

Lemma ForallE {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.
End ForallNorm.
Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : 
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  elim: l; [constructor; by constructor | ].
  move=> ? ? IH /=. constructor => /ForallE [? /IH ?]; by constructor.
Qed.

Lemma filter_length_le {X: Type} f g (L: list X) :
  (forall x, f x = true -> g x = true) ->
  length (filter f L) <= length (filter g L).
Proof.
  move=> Hfg. elim: L; first done.
  move=> x L IH /=.
  move: (f x) (Hfg x) => [].
  - move=> -> /=; [done|lia].
  - case: (g x) => /=; lia.
Qed.

Lemma filter_length_lt {X: Type} {f g} {L: list X} {x} :
  (forall x, f x = true -> g x = true) ->
  In x L -> f x = false -> g x = true ->
  length (filter f L) < length (filter g L).
Proof.
  move=> Hfg + Hfx Hgx. elim: L; first done.
  move=> y L IH /= [->|].
  - rewrite Hfx Hgx /=.
    move: Hfg => /filter_length_le => /(_ L). lia.
  - move=> /IH {}IH. move: (f y) (Hfg y) => [].
    + move=> -> /=; [done|lia].
    + case: (g y) => /=; lia.
Qed.

Section DECIDRE.

Variable M : Mm2.

Notation step := (MM2.step M).
Notation multi_step := (MM2.multi_step M).
Notation terminating := (MM2.terminating M).
Notation l := (length M).

(* after k steps values change at most by k (or are reset and at most k) *)
Lemma multi_step_bound {k p a b p' a' b'} : multi_step k (p, (a, b)) = Some (p', (a', b')) -> 
  a' <= k + a /\ b' <= k + b /\ (a' <= k \/ a <= k + a') /\ (b' <= k \/ b <= k + b').
Proof.
  elim: k p' a' b'.
  { move=> p' a' b' /= []. lia. }
  move=> k + p' a' b' /=.
  case: (multi_step k (p, (a, b))) => [[p'' [a'' b'']]|]; last done.
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

Definition reaches (x y: Config) := exists k, multi_step k x = Some y.
Definition reaches_plus (x y: Config) := exists k, 0 < k /\ multi_step k x = Some y.
Definition non_terminating x := forall k, multi_step k x <> None.

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

Lemma reaches_terminating {x y} : reaches x y -> terminating y -> terminating x.
Proof.
  move=> [k Hk] [k' Hk']. exists (k+k').
  move: Hk. by rewrite /multi_step iter_plus => ->.
Qed.

Lemma multi_step_k_monotone {k x} k' : multi_step k x = None -> k <= k' -> multi_step k' x = None.
Proof.
  move=> + ?. have ->: k' = (k' - k) + k by lia.
  elim: (k' - k); first done.
  by move=> ? IH /IH /= ->.
Qed.

Lemma multi_step_plus {k x k' y} :
multi_step k x = Some y -> multi_step (k + k') x = multi_step k' y.
Proof. rewrite /multi_step iter_plus. by move=> ->. Qed.

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

Lemma reaches_plus_state_bound {x y} : reaches_plus x y -> state x < l.
Proof.
  move=> [k [? Hk]].
  suff: not (l <= state x) by lia.
  move=> /nth_error_None Hx.
  move: Hk. have ->: k = S (k - 1) by lia.
  by rewrite /= option_bind_iter /step Hx iter_None.
Qed.

Lemma reaches_plus_trans {x y z} : reaches_plus x y -> reaches_plus y z -> reaches_plus x z.
Proof. by move=> /reaches_plus_incl /reaches_reaches_plus H /H. Qed.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. move=> [k Hk] [k' Hk']. exists (k+k'). by rewrite (multi_step_plus Hk). Qed.

(* a configuration (p, (a, b))
  is either halting or uniformly transitions into a configuration with one zero counter *)
Lemma next_waypoint p a b :
  terminating (p, (a, b)) +
  { '(p', a') | forall n, exists k, 0 < k <= l - p /\ multi_step k (p, (n+a, b)) = Some (p', (n+a', 0)) } +
  { '(p', b') | forall n, exists k, 0 < k <= l - p /\ multi_step k (p, (a, n+b)) = Some (p', (0, n+b')) }.
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
        apply: multi_step_plus. by rewrite /= /step Hi.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
    + move=> Hi.
      have [[|[[p' a'] HSp]]|[[p' b'] HSp]] := IH (S p) ltac:(lia) (S a) b.
      * move=> /reaches_terminating HSp. left. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * left. right. exists (p', a').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi.
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
        apply: multi_step_plus. by rewrite /= /step Hi.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
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
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
      * right. exists (p', b').
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi.
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
    have ? := multi_step_bound Hk.
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
    have ? := multi_step_bound Hk.
    split; [by exists k|lia].
  - left. right. exists (p', b') => n.
    have [k [? Hk]] := Hp n. exists k.
    split; [lia|done].
Qed.

(*
Lemma distinct_states x L :
  Forall (fun y => reaches x y) L -> NoDup (map state L) -> length L <= l+l+2.
Proof.
  move=> /Forall_forall HL.
  suff : incl (map state L) ([state x] ++ (seq 0 (l+1)) ++ (map (fun i => if i is dec _  q then q else 0) M)).
  { move=> /NoDup_incl_length H /H. rewrite ?app_length ?map_length seq_length /=. lia. }
  move=> p' /in_map_iff [y [<-]] /HL [[|k]].
  { move=> /= [->]. by left. }
  move=> /=. case: (multi_step k x); last done.
  move=> [p [a b]]. rewrite /= /step.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; last done.
  have ? : p < l by (apply /nth_error_Some; move: Hi => /= ->).
  case: i Hi.
  - done.
  - move=> ? _ [<-] /=. right. apply /in_app_iff. left. apply /in_seq. lia.
  - move=> ? _ [<-] /=. right. apply /in_app_iff. left. apply /in_seq. lia.
  - move=> [] q /= Hi.
    + move: b => [|b].
      * move=> [<-] /=. right. apply /in_app_iff. right. apply /in_map_iff.
        exists (dec true q). split; first done. apply /nth_error_In. eassumption.
      * move=> [<-] /=. right. apply /in_app_iff. left. apply /in_seq. lia.
    + move: a => [|a].
      * move=> [<-] /=. right. apply /in_app_iff. right. apply /in_map_iff.
        exists (dec false q). split; first done. apply /nth_error_In. eassumption.
      * move=> [<-] /=. right. apply /in_app_iff. left. apply /in_seq. lia.
Qed.
*)

(*
(* if b remains strictly positive throughout a computation, 
  then a is bounded by max l (a + (l - p)) *)
Lemma multi_step_ubound_a p a b k :
  (forall k', k' <= k ->
    match multi_step k' (p, (a, b)) with
    | None => True
    | Some (p', (a', b')) => 0 < b'
    end) ->
  (forall k', k' <= k ->
    match multi_step k' (p, (a, b)) with
    | None => True
    | Some (p', (a', b')) => a' <= Nat.max l (a + (l - p))
    end).
Proof.
  elim: k p a b.
  { move=> p a b _ [|?] ? /=; lia. }
  move=> k IH p a b /= Hpab [|k'].
  { move=> /=. lia. }
  rewrite /= option_bind_iter /step.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; last by rewrite iter_None.
  have U : forall (A B C : Prop), (B -> C) -> A -> (A -> B) -> C by tauto.
  have ? : l > p.
  { suff: not (l <= p) by lia.
    move=> /nth_error_None. by move: Hi => /= ->. }
  rewrite -/step => ?. case: i Hi.
  - by rewrite iter_None.
  - case.
    + (* zero b *)
      move=> Hi. rewrite /= -/(multi_step _ _).
      have := IH (S p) a 0 _ k' ltac:(lia).
      case: (multi_step k' (S p, (a, 0))); last done.
      move=> [p' [a' b']]. apply: U; first by lia.
      move=> k'' ?.
      have := Hpab (S k'') ltac:(lia).
      by rewrite /= option_bind_iter /step Hi.
    + (* zero a *)
      move=> Hi. rewrite /= -/(multi_step _ _).
      have := IH (S p) 0 b _ k' ltac:(lia).
      case: (multi_step k' (S p, (0, b))); last done.
      move=> [p' [a' b']]. apply: U; first by lia.
      move=> k'' ?.
      have := Hpab (S k'') ltac:(lia).
      by rewrite /= option_bind_iter /step Hi.
  - case.
    + (* inc b *)
      move=> Hi. rewrite /= -/(multi_step _ _).
      have := IH (S p) a (S b) _ k' ltac:(lia).
      case: (multi_step k' (S p, (a, S b))); last done.
      move=> [p' [a' b']]. apply: U; first by lia.
      move=> k'' ?.
      have := Hpab (S k'') ltac:(lia).
      by rewrite /= option_bind_iter /step Hi.
    + (* inc a *)
      move=> Hi. rewrite /= -/(multi_step _ _).
      have := IH (S p) (S a) b _ k' ltac:(lia).
      case: (multi_step k' (S p, (S a, b))); last done.
      move=> [p' [a' b']]. apply: U; first by lia.
      move=> k'' ?.
      have := Hpab (S k'') ltac:(lia).
      by rewrite /= option_bind_iter /step Hi.
  - move=> [] q.
    + (* dec b *)
      move=> Hi.
      move: b Hpab Hi => [|b].
      { move=> /(_ 0 ltac:(lia)) /=. lia. }
      move=> Hpab Hi.
      have := IH (S p) a b _ k' ltac:(lia).
      rewrite /= -/(multi_step _ _).
      case: (multi_step k' (S p, (a, b))); last done.
      move=> [p' [a' b']]. apply: U; first by lia.
      move=> k'' ?.
      have := Hpab (S k'') ltac:(lia).
      by rewrite /= option_bind_iter /step Hi.
    + (* dec a *)
      move=> Hi.
      move: a Hpab Hi => [|a].
      * move=> Hpab Hi /=.
        have := IH q 0 b _ k' ltac:(lia).
        rewrite /= -/(multi_step _ _).
        case: (multi_step k' (q, (0, b))); last done.
        move=> [p' [a' b']]. apply: U; first by lia.
        move=> k'' ?.
        have := Hpab (S k'') ltac:(lia).
        by rewrite /= option_bind_iter /step Hi.
      * move=> Hpab Hi.
        have := IH (S p) a b _ k' ltac:(lia).
        rewrite /= -/(multi_step _ _).
        case: (multi_step k' (S p, (a, b))); last done.
        move=> [p' [a' b']]. apply: U; first by lia.
        move=> k'' ?.
        have := Hpab (S k'') ltac:(lia).
        by rewrite /= option_bind_iter /step Hi.
Qed.
*)

Inductive R : list (nat*nat) -> list (nat*nat) -> Prop :=
  R_lt L p c : p < l -> Forall (fun '(p', c') => p = p' -> c < c') L -> R ((p, c)::L) L.

Lemma wf_R : well_founded R.
Proof.
  move=> L.
  pose f := fun (L' : list (nat * nat)) => (length (filter (fun p => 
    match in_dec Nat.eq_dec p (map fst L') with
    | left _ => false
    | right _ => true
    end) (seq 0 l))).
  elim /(measure_ind f): L.
  move=> L IH. constructor => ? HL.
  move: HL IH => [] {}L p c ? HL IH.
  have [Hp|Hp] := in_dec Nat.eq_dec p (map fst L).
  - admit. (*hard*)
  - apply: IH. rewrite /f [map fst _]/=.
    have: In p (seq 0 l) by apply /in_seq; lia.
    move=> /filter_length_lt. apply.
    + move=> q. case: (in_dec Nat.eq_dec q (p :: map fst L)); first done.
      move=> Hq _. case: (in_dec Nat.eq_dec q (map fst L)); last done.
      move: Hq => /=. tauto.
    + rewrite /=. case: (Nat.eq_dec p p); [done|lia].
    + by case: (in_dec _ _ _).
Admitted.

Lemma find_element (L : list (nat*nat)) p c :
  (Forall (fun '(p', c') => p = p' -> c < c') L) + (exists c', In (p, c') L /\ c' <= c).
Proof.
  elim: L; first by left.
  move=> [p' c'] L [IH|IH].
  - have [<-|?] := Nat.eq_dec p p'.
    + have [?|?] := Nat.eq_dec (c'-c) 0.
      * right. exists c'. split; [by left|lia].
      * left. constructor; [lia|done].
    + left. constructor; [lia|done].
  - right. move: IH => [c'' [? ?]]. exists c''.
    split; [by right|lia].
Qed.

Lemma loop_a {p a a' b} :
  a <= a' ->
  (forall n : nat, reaches_plus (p, (n + a, b)) (p, (n + a', b))) ->
  non_terminating (p, (a, b)).
Proof.
  move=> ? Hp k.
  suff: forall m, multi_step k (p, (m + a, b)) <> None by move=> /(_ 0).
  elim: k; first done.
  move=> k IH m.
  have [k' [? Hk']] := Hp m.
  move=> /(multi_step_k_monotone (k' + k)) /(_ ltac:(lia)).
  move: Hk' => /multi_step_plus ->.
  have ->: m + a' = (m + a' - a) + a by lia.
  by apply: IH.
Qed.

Lemma loop_b {p a b b'} :
  b <= b' ->
  (forall n : nat, reaches_plus (p, (a, n + b)) (p, (a, n + b'))) ->
  non_terminating (p, (a, b)).
Proof.
  move=> ? Hp k.
  suff: forall m, multi_step k (p, (a, m + b)) <> None by move=> /(_ 0).
  elim: k; first done.
  move=> k IH m.
  have [k' [? Hk']] := Hp m.
  move=> /(multi_step_k_monotone (k' + k)) /(_ ltac:(lia)).
  move: Hk' => /multi_step_plus ->.
  have ->: m + b' = (m + b' - b) + b by lia.
  by apply: IH.
Qed.

Lemma reaches_plus_self_loop x : reaches_plus x x -> non_terminating x.
Proof.
  move=> [k [? Hk]]. elim; first done.
  move=> k' Hk'.
  move=> /(multi_step_k_monotone (k + k')) /(_ ltac:(lia)).
  by rewrite (multi_step_plus Hk).
Qed.

Lemma big_wf_a p a (L : list (nat*nat)) :
  Forall (fun '(p', a') => forall n, reaches_plus (p', (n+a', 0)) (p, (n+a, 0))) L -> 
  terminating (p, (a, 0)) +
  non_terminating (p, (a, 0)) +
  { '(p', (a', b')) | reaches (p, (a, 0)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  elim /(well_founded_induction_type wf_R) : L p a.
  move=> L IH p a HL.
  have [[Hp|[[p' a'] Hp]]|[[p' [a' b']] [Hp ?]]] := next_waypoint_a p a.
  - left. by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    have [H'L|H'L] := find_element L p a.
    + have /IH : R ((p, a)::L) L by constructor.
      move=> /(_ p' a') /=. case; [|case|].
      * constructor; first done.
        apply: Forall_impl HL => - [p'' a''] Hp'' n.
        by apply /(reaches_plus_trans (Hp'' n)) /Hp.
      * move=> /reaches_terminating Hp'. left. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> /reaches_non_terminating Hp'. left. right.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> [[p'' [a'' b'']]] [Hp'] ?. right.
        exists (p'', (a'', b'')). split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))).
    + left. right. move: H'L => [a''] [Ha'' ?].
      move: HL Ha'' => /Forall_forall HL /HL{HL} H'p.
      apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
      by apply: (loop_a _ H'p).
  - right. by exists (p', (a', b')).
Qed.

Lemma big_wf_b p b (L : list (nat*nat)) :
  Forall (fun '(p', b') => forall n, reaches_plus (p', (0, n+b')) (p, (0, n+b))) L -> 
  terminating (p, (0, b)) +
  non_terminating (p, (0, b)) +
  { '(p', (a', b')) | reaches (p, (0, b)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  elim /(well_founded_induction_type wf_R) : L p b.
  move=> L IH p b HL.
  have [[Hp|[[p' b'] Hp]]|[[p' [a' b']] [Hp ?]]] := next_waypoint_b p b.
  - left. by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    have [H'L|H'L] := find_element L p b.
    + have /IH : R ((p, b)::L) L by constructor.
      move=> /(_ p' b') /=. case; [|case|].
      * constructor; first done.
        apply: Forall_impl HL => - [p'' b''] Hp'' n.
        by apply /(reaches_plus_trans (Hp'' n)) /Hp.
      * move=> /reaches_terminating Hp'. left. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> /reaches_non_terminating Hp'. left. right.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> [[p'' [a'' b'']]] [Hp'] ?. right.
        exists (p'', (a'', b'')). split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))).
    + left. right. move: H'L => [b''] [Hb'' ?].
      move: HL Hb'' => /Forall_forall HL /HL{HL} H'p.
      apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
      by apply: (loop_b _ H'p).
  - right. by exists (p', (a', b')).
Qed.

(* from any config can decide or get to next small waypoint *)
Lemma next_small_waypoint p a b :
  terminating (p, (a, b)) +
  non_terminating (p, (a, b)) +
  { '(p', (a', b')) | reaches_plus (p, (a, b)) (p', (a', b')) /\ a' <= l /\ b' <= l }.
Proof.
  have [[?|[[p' a'] Hp]]|[[p' b'] Hp]] := next_waypoint p a b.
  - left. by left.
  - have [[|]|] := big_wf_a p' a' [] ltac:(done).
    * move=> /reaches_terminating Hp'. left. left.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> /reaches_non_terminating Hp'. left. right.
      apply: Hp'. have [k [? Hk]] := Hp 0. by exists k.
    * move=> [[p'' [a'' b'']]] [Hp'] ?. right.
      exists (p'', (a'', b'')). split; last done.
      apply: (reaches_plus_reaches _ Hp').
      have [k [? Hk]] := Hp 0. exists k. split; [lia|done].
  - have [[|]|] := big_wf_b p' b' [] ltac:(done).
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

End DECIDRE.

Print Assumptions uniform_decision.

(* decision procedure for the halting problem for Mm2 *)
Definition decider (M: Mm2) (c: Config) : bool :=
  match uniform_decision M c with
  | inl _ => true
  | inr _ => false
  end.

(* decision procedure correctness *)
Lemma decider_spec (M: Mm2) (c: Config) :
  (decider M c = true) <-> (terminating M c).
Proof.
  rewrite /decider. case: (uniform_decision M c).
  - tauto.
  - move=> H. split; [done | by move=> [k /H]].
Qed.

Theorem MM2_HALT_dec :
  exists f : Mm2 * Config -> bool,
  forall X, f X = true <-> MM2_HALT X.
Proof.
  exists (fun '(M, c) => decider M c).
  intros [M c]. exact (decider_spec M c).
Qed.
