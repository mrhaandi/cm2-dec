(* decider for MM2 halting *)

Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect.
Require Import CM2.MM2.

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

(* 
  from any configuration (p, (a, b)) in k steps such that 0 < k <= l + 1 steps
  one can get to either 
  - a halting configuration
  - a small configuration (both counter < l )
  - a configuration where one of the counters is 0 and the other did not decrease much
*)

Lemma next_waypoint p a b :
  (exists k, 0 < k <= l - p + 1 /\ 
    match multi_step k (p, (a, b)) with
    | None => True
    | Some (q, (a', b')) => 
        (a' <= l /\ b' <= l) \/ 
        (a' = 0 /\ b + p <= b' + l) \/
        (b' = 0 /\ a + p <= a' + l)
    end).
Proof.
  move: a b. move Hn: (l - p) => n. elim: n p Hn.
  { move=> p Hp a b. exists 1 => /=.
    split; first by lia. rewrite /step.
    by have /nth_error_None -> : l <= p by lia. }
  move=> n IH p Hp a b.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; first last.
  { exists 1. rewrite /= /step Hi. lia. }
  case: i Hi.
  - move=> Hi. exists 1. rewrite /= /step Hi. lia.
  - case.
    + (* zero b *)
      move=> Hi. exists 1. rewrite /= /step Hi /=. lia.
    + (* zero a *)
      move=> Hi. exists 1. rewrite /= /step Hi /=. lia.
  - move=> [] Hi.
    + (* inc b *)
      have [k [? Hk]] := IH (S p) ltac:(lia) a (S b).
      exists (1 + k).
      rewrite /multi_step iter_plus /= /step Hi -/step /= -/(multi_step _ _).
      split; first by lia.
      case: (multi_step k (S p, (a, S b))) Hk; last done.
      move=> [? [? ?]]. lia.
    + (* inc a *)
      have [k [? Hk]] := IH (S p) ltac:(lia) (S a) b.
      exists (1 + k).
      rewrite /multi_step iter_plus /= /step Hi -/step /= -/(multi_step _ _).
      split; first by lia.
      case: (multi_step k (S p, (S a, b))) Hk; last done.
      move=> [? [? ?]]. lia.
  - move=> [] q.
    + (* dec b *)
      move: b => [|b] Hi.
      { exists 1. rewrite /= /step Hi /=. lia. }
      have [k [? Hk]] := IH (S p) ltac:(lia) a b.
      exists (1 + k). split; first by lia.
      rewrite /multi_step iter_plus /= /step Hi -/step /= -/(multi_step _ _).
      case: (multi_step k (S p, (a, b))) Hk; last done.
      move=> [? [? ?]]. lia.
    + (* dec a *)
      move: a => [|a] Hi.
      { exists 1. rewrite /= /step Hi /=. lia. }
      have [k [? Hk]] := IH (S p) ltac:(lia) a b.
      exists (1 + k). split; first by lia.
      rewrite /multi_step iter_plus /= /step Hi -/step /= -/(multi_step _ _).
      case: (multi_step k (S p, (a, b))) Hk; last done.
      move=> [? [? ?]]. lia.
Qed.

(* parallel run *)
Lemma parallel_b {k p a b p' a' b'} : multi_step k (p, (a, b)) = Some (p', (a', b')) -> k < b ->
  (exists k' p'' a'', k' <= k /\ multi_step k' (p, (a, b)) = Some (p'', (a'', 0))) \/
  forall n, multi_step k (p, (a, n+b)) = Some (p', (a', n+b')).
Proof.
  elim: k p a b.
  { move=> p a b /= [] *. subst. by right. }
  move=> k IH p a b.
  rewrite /= option_bind_iter.
  rewrite /step. case Hi: (nth_error M (state (p, (a, b)))) => [i|]; last by rewrite iter_None.
  rewrite -/step. case: i Hi.
  - by rewrite iter_None.
  - case.
    + (* zero b *)
      move=> /= Hi ? ?. left. exists 1, (S p), a.
      split; first by lia. by rewrite /= /step Hi.
    + (* zero a *)
      move=> /= Hi /IH {}IH ?.
      have /IH [[k' [p'' [a'' [? H]]]]|] : k < b by lia.
      * left. exists (S k'), p'', a''. split; first by lia.
        have -> : S k' = 1 + k' by lia. rewrite /(multi_step (1+k')) iter_plus /=.
        by rewrite /step Hi /= -/step -H.
      * move=> H. right. move=> k'. by rewrite option_bind_iter /step Hi -/step -H.
  Admitted.

Lemma parallel_a {k p a b p' a' b'} : multi_step k (p, (a, b)) = Some (p', (a', b')) -> k < a ->
  (exists k' p'' b'', k' <= k /\ multi_step k' (p, (a, b)) = Some (p'', (0, b''))) \/
  forall n, multi_step k (p, (n+a, b)) = Some (p', (n+a', b')).
Proof. Admitted.

(*
(* todo needs waypoint after l not l+1 steps? or small bound set to l+1? *)
Corollary next_waypoint_b p b : b > l + 1 ->
  (exists k, 0 < k <= l + 1 /\ 
    (multi_step k (p, (0, b)) = None \/
    (exists p' b', multi_step k (p, (0, b)) = Some (p', (0, b')) /\ b <= b' + l) \/
    exists p' a' b', multi_step k (p, (0, b)) = Some (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1)).
Proof.
  move=> ?. have [k [? Hk]] := next_waypoint p 0 b.
  exists k. split; first by lia.
  move: Hk. case E: (multi_step k (p, (0, b))) => [[p' [a' b']]|]; last by tauto.
  move=> [?|[?|?]]; right.
  - right. exists p', a', b'. split; [done|lia].
  - left. exists p', b'. split; last by lia.
    congr (Some (p', (_, b'))). tauto.
  - have [?|?] : a' <= l + 1 \/ l + 1 < a' by lia.
    + right. exists p', a', 0. split; last by lia.
      congr (Some (p', (a', _))). tauto.
    + have := asd E. lia.
Qed.
*)

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

(*
Lemma best_next_waypoint p a b :
  terminating (p, (a, b)) \/
  (exists p' a', forall n, reaches_plus (p, (n+a, b)) (p', (n+a', 0))) \/
  (exists p' b', forall n, reaches_plus (p, (a, n+b)) (p', (0, n+b'))).
Proof.
  move Hn: (l - p) => n. elim: n p Hn a b.
  { move=> p ? a b. left. exists 1. rewrite /= /step.
    by have ->: nth_error M (state (p, (a, b))) = None
      by (rewrite nth_error_None /=; lia). }
  move=> n IH p ? a b.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; first last.
  { left. exists 1. by rewrite /= /step Hi. }
  move: i Hi => /= [].
  - move=> Hi. left. exists 1. by rewrite /= /step Hi.
  - case.
    + move=> Hi. right. left. exists (S p), a.
      move=> n'. exists 1. split; first done.
      by rewrite /= /step /= Hi.
    + admit.
  - case.
    + move=> Hi.
      have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) a (S b).
      * move=> /reaches_terminating HSp. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * right. left. exists p', a'.
        move=> n'. apply: (reaches_plus_trans _ (HSp n')).
        exists 1. split; first done.
        by rewrite /= /step Hi.
      * do 2 right. exists p', a'.
        move=> n'. apply: (reaches_plus_trans _ (HSp n')).
        exists 1. split; first done.
        by rewrite /= /step Hi Nat.add_succ_r.
    + admit.
  - case=> q Hi.
    + move: b => [|b].
      { right. left. exists q, a => n'. exists 1. 
        split; first done. by rewrite /= /step Hi. }
      have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) a b.
      * move=> /reaches_terminating HSp. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * right. left. exists p', a'.
        move=> n'. apply: (reaches_plus_trans _ (HSp n')).
        exists 1. split; first done.
        by rewrite /= /step Hi.
      * do 2 right. exists p', a'.
        move=> n'. apply: (reaches_plus_trans _ (HSp n')).
        exists 1. split; first done.
        by rewrite /= /step Hi Nat.add_succ_r.
    + admit.
Admitted.
*)

Lemma best_next_waypoint p a b :
  terminating (p, (a, b)) \/
  (exists p' a', forall n, exists k, 0 < k < (l - p) + 1 /\ multi_step k (p, (n+a, b)) = Some (p', (n+a', 0))) \/
  (exists p' b', forall n, exists k, 0 < k < (l - p) + 1 /\ multi_step k (p, (a, n+b)) = Some (p', (0, n+b'))).
Proof.
  move Hn: (l - p) => n. elim: n p Hn a b.
  { move=> p ? a b. left. exists 1. rewrite /= /step.
    by have ->: nth_error M (state (p, (a, b))) = None
      by (rewrite nth_error_None /=; lia). }
  move=> n IH p ? a b.
  case Hi: (nth_error M (state (p, (a, b)))) => [i|]; first last.
  { left. exists 1. by rewrite /= /step Hi. }
  move: i Hi => /= [].
  - move=> Hi. left. exists 1. by rewrite /= /step Hi.
  - case.
    + move=> Hi. right. left. exists (S p), a.
      move=> n'. exists 1. split; first by lia.
      by rewrite /= /step /= Hi.
    + move=> Hi. do 2 right. exists (S p), b.
      move=> n'. exists 1. split; first by lia.
      by rewrite /= /step /= Hi.
  - case.
    + move=> Hi.
      have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) a (S b).
      * move=> /reaches_terminating HSp. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * right. left. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi.
      * do 2 right. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
    + move=> Hi.
      have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) (S a) b.
      * move=> /reaches_terminating HSp. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * right. left. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
      * do 2 right. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi.
  - case=> q Hi.
    + move: b => [|b].
      { right. left. exists q, a => n'. exists 1. 
        split; first by lia. by rewrite /= /step Hi. }
      have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) a b.
      * move=> /reaches_terminating HSp. left.
        apply: HSp. exists 1. by rewrite /= /step Hi.
      * right. left. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi.
      * do 2 right. exists p', a'.
        move=> n'.
        have [k [? <-]] := (HSp n').
        exists (1+k). split; first by lia.
        apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
    + move: a => [|a].
        { do 2 right. exists q, b => n'. exists 1. 
          split; first by lia. by rewrite /= /step Hi. }
        have [|[[p' [a' HSp]]|[p' [a' HSp]]]] := IH (S p) ltac:(lia) a b.
        * move=> /reaches_terminating HSp. left.
          apply: HSp. exists 1. by rewrite /= /step Hi.
        * right. left. exists p', a'.
          move=> n'.
          have [k [? <-]] := (HSp n').
          exists (1+k). split; first by lia.
          apply: multi_step_plus. by rewrite /= /step Hi Nat.add_succ_r.
        * do 2 right. exists p', a'.
          move=> n'.
          have [k [? <-]] := (HSp n').
          exists (1+k). split; first by lia.
          apply: multi_step_plus. by rewrite /= /step Hi.
Qed.

(*
Lemma best_next_waypoint p a b :
  terminating (p, (a, b)) \/
  (exists p' a', forall n, reaches_plus (p, (n+a, b)) (p', (n+a', 0))) \/
  (exists p' b', forall n, reaches_plus (p, (a, n+b)) (p', (0, n+b'))) \/
  exists p' a' b', reaches (p, (a, b)) (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1.
Proof.
  have [?|?] : a <= l + 1 \/ a > l + 1 by lia.
  { do 2 right. exists p, a, 0. split; [by exists 0 | lia]. }
  have [k [? Hk]] := next_waypoint p a 0.
Admitted.
*)

(* terminate or reach uniformly next config or reach small config *)
Corollary next_waypoint_a p a :
  terminating (p, (a, 0)) \/
  (exists p' a', forall n, reaches_plus (p, (n+a, 0)) (p', (n+a', 0))) \/
  exists p' a' b', reaches (p, (a, 0)) (p', (a', b')) /\ a' <= l /\ b' <= l.
Proof.
  have [?|[[p' [a' Hp]]|[p' [b' Hp]]]] := best_next_waypoint p a 0.
  - by left.
  - right. left. exists p', a' => n.
    have [k [? Hk]] := Hp n. exists k.
    split; [lia|done].
  - do 2 right. exists p', 0, b'.
    have [k [? Hk]] := Hp 0.
    have ? := multi_step_bound Hk.
    split; [by exists k|lia].
Qed.

(*
  move: Hk. case E: (multi_step k (p, (0, b))) => [[p' [a' b']]|]; first last.
  { move=> _. left. by exists k. }
  move=> [?|[?|?]]; right.
  - right. exists p', a', b'. split; [|lia]. by exists k.
  - move: E => /parallel_b => /(_ ltac:(lia)) [].
    + move=> [k' [p'' [a'' [?]]]] Hk'.
      move: (Hk') => /multi_step_bound ?. right.
      exists p'', a'', 0. split; last by lia.
      by exists k'.
    + move=> H. left. exists p', b' => n. exists k. split; first by lia.
      rewrite (H n). congr (Some (p', (_, n + b'))). lia.
  - right. exists p', a', 0.
    move: (E) => /multi_step_bound ?.
    split; last by lia.
    exists k. rewrite E. congr (Some (p', (a', _))). lia.
Qed.
*)

(* terminate or reach uniformly next config or reach small config *)
Corollary next_waypoint_b p b :
  terminating (p, (0, b)) \/
  (exists p' b', forall n, reaches_plus (p, (0, n+b)) (p', (0, n+b'))) \/
  exists p' a' b', reaches (p, (0, b)) (p', (a', b')) /\ a' <= l /\ b' <= l.
Proof.
  have [?|[[p' [a' Hp]]|[p' [b' Hp]]]] := best_next_waypoint p 0 b.
  - by left.
  - do 2 right. exists p', a', 0.
    have [k [? Hk]] := Hp 0.
    have ? := multi_step_bound Hk.
    split; [by exists k|lia].
  - right. left. exists p', b' => n.
    have [k [? Hk]] := Hp n. exists k.
    split; [lia|done].
Qed.

(*
Corollary next_waypoint_a p a : a > l + 1 ->
  (exists k, 0 < k <= l + 1 /\ 
    (multi_step k (p, (a, 0)) = None \/
    (exists p' a', multi_step k (p, (a, 0)) = Some (p', (a', 0)) /\ a <= a' + l) \/
    exists p' a' b', multi_step k (p, (a, 0)) = Some (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1)).
Proof.
  move=> ?. have [k [? Hk]] := next_waypoint p a 0.
  exists k. split; first by lia.
  move: Hk. case E: (multi_step k (p, (a, 0))) => [[p' [a' b']]|]; last by tauto.
  move=> [?|[?|?]]; right.
  - right. exists p', a', b'. split; [done|lia].
  - have [?|?] : b' <= l + 1 \/ l + 1 < b' by lia.
    + right. exists p', 0, b'. split; last by lia.
      congr (Some (p', (_, b'))). tauto.
    + have := asd E. lia.
  - left. exists p', a'. split; last by lia.
    congr (Some (p', (a', _))). tauto.
Qed.
*)


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
Admitted. (* this is difficult *)

Lemma find_element (L : list (nat*nat)) p c :
  (Forall (fun '(p', c') => p = p' -> c < c') L) \/ (exists c', In (p, c') L /\ c' <= c).
Proof.
  elim: L; first by left.
  move=> [p' c'] L [IH|[c'' [? ?]]].
  - have [?|?] : (p = p' -> c < c') \/ (not (p = p' -> c < c')) by lia.
    + left. by constructor.
    + right. exists c'. split; [left; congr pair|]; lia.
  - right. exists c''. split; [by right | lia].
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
  terminating (p, (a, 0)) \/
  non_terminating (p, (a, 0)) \/
  (exists p' a' b', reaches (p, (a, 0)) (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1).
Proof.
  elim /(well_founded_ind wf_R) : L p a.
  move=> L IH p a HL.
  have [Hp|[[p' [a' Hp]]|[p' [a' [b' [Hp ?]]]]]] := next_waypoint_a p a.
  - by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    have [H'L|] := find_element L p a.
    + have /IH : R ((p, a)::L) L by constructor.
      move=> /(_ p' a') /=. case; last case.
      * constructor; first done.
        apply: Forall_impl HL => - [p'' a''] Hp'' n.
        by apply /(reaches_plus_trans (Hp'' n)) /Hp.
      * move=> /reaches_terminating Hp'. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> /reaches_non_terminating Hp'. right. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> [p''] [a''] [b''] [Hp'] ?. do 2 right.
        exists p'', a'', b''. split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))).
    + move=> [a''] [Ha'' ?]. right. left.
      move: HL Ha'' => /Forall_forall HL /HL{HL} H'p.
      apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
      by apply: (loop_a _ H'p).
  - do 2 right. exists p', a', b'. split; [done|lia].
Qed.

Lemma big_wf_b p b (L : list (nat*nat)) :
  Forall (fun '(p', b') => forall n, reaches_plus (p', (0, n+b')) (p, (0, n+b))) L -> 
  terminating (p, (0, b)) \/
  non_terminating (p, (0, b)) \/
  (exists p' a' b', reaches (p, (0, b)) (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1).
Proof.
  elim /(well_founded_ind wf_R) : L p b.
  move=> L IH p b HL.
  have [Hp|[[p' [b' Hp]]|[p' [a' [b' [Hp ?]]]]]] := next_waypoint_b p b.
  - by left.
  - have /= ? := reaches_plus_state_bound (Hp 0).
    have [H'L|] := find_element L p b.
    + have /IH : R ((p, b)::L) L by constructor.
      move=> /(_ p' b') /=. case; last case.
      * constructor; first done.
        apply: Forall_impl HL => - [p'' b''] Hp'' n.
        by apply /(reaches_plus_trans (Hp'' n)) /Hp.
      * move=> /reaches_terminating Hp'. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> /reaches_non_terminating Hp'. right. left.
        by apply /Hp' /reaches_plus_incl /(Hp 0).
      * move=> [p''] [a''] [b''] [Hp'] ?. do 2 right.
        exists p'', a'', b''. split; last done.
        by apply: (reaches_trans (reaches_plus_incl (Hp 0))).
    + move=> [b''] [Hb'' ?]. right. left.
      move: HL Hb'' => /Forall_forall HL /HL{HL} H'p.
      apply: (reaches_non_terminating' (reaches_plus_incl (H'p 0))).
      by apply: (loop_b _ H'p).
  - do 2 right. exists p', a', b'. split; [done|lia].
Qed.

(* from any config can decide or get to next small waypoint *)
Lemma next_small_waypoint p a b :
  terminating (p, (a, b)) \/
  non_terminating (p, (a, b)) \/
  (exists p' a' b', reaches_plus (p, (a, b)) (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1).
Proof.
  have [k [?]] := next_waypoint p a b.
  case E: (multi_step k (p, (a, b))) => [[p' [a' b']]|]; first last.
  { move=> _. left. by exists k. }
  case; last case.
  - move=> ?. do 2 right. exists p', a', b'.
    split; last by lia.
    exists k. split; [lia|done].
  - move=> [? ?]. subst a'.
    have [|[|]] := big_wf_b p' b' [] ltac:(done).
    * move=> /reaches_terminating Hp'. left.
      apply: Hp'. by exists k.
    * move=> /reaches_non_terminating Hp'. right. left.
      apply: Hp'. by exists k.
    * move=> [p''] [a''] [b''] [Hp'] ?. do 2 right.
      exists p'', a'', b''. split; last done.
      apply: (reaches_plus_reaches _ Hp').
      exists k. split; [lia|done].
  - move=> [? ?]. subst b'.
    have [|[|]] := big_wf_a p' a' [] ltac:(done).
    * move=> /reaches_terminating Hp'. left.
      apply: Hp'. by exists k.
    * move=> /reaches_non_terminating Hp'. right. left.
      apply: Hp'. by exists k.
    * move=> [p''] [a''] [b''] [Hp'] ?. do 2 right.
      exists p'', a'', b''. split; last done.
      apply: (reaches_plus_reaches _ Hp').
      exists k. split; [lia|done].
Qed.

Lemma small_decider p a b L : a <= l + 1 -> b <= l + 1 ->
  Forall (fun '(p', (a', b')) => reaches_plus (p', (a', b')) (p, (a, b)) /\ p' < l /\ a' <= l + 1 /\ b' <= l + 1 ) L ->
  NoDup L ->
  terminating (p, (a, b)) \/ non_terminating (p, (a, b)).
Proof.
  move Hn: ((l*(l+2)*(l+2)+1) - length L) => n.
  elim: n L Hn p a b.
  { move=> L ? ????? H1L /NoDup_incl_length H2L.
    have : incl L (list_prod (seq 0 l) (list_prod (seq 0 (l+2)) (seq 0 (l+2)))).
    { move=> [p [a b]].
      move: H1L => /Forall_forall H1L /H1L ?.
      apply /in_prod; [|apply /in_prod]; apply /in_seq; lia. }
    move=> /H2L. rewrite ?prod_length ?seq_length. lia. }
  move=> n IH L ? p a b ? ? H1L H2L.
  have [|[|[p' [a' [b' [Hp ?]]]]]] := next_small_waypoint p a b; [tauto|tauto|].
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

Lemma decider x : terminating x \/ non_terminating x.
Proof.
  move: x => [p [a b]].
  have [|[|]] := next_small_waypoint p a b; [tauto|tauto|].
  move=> [p'] [a'] [b'] [/reaches_plus_incl Hp'] [Ha' Hb'].
  have := small_decider p' a' b' [] Ha' Hb'. case.
  - by constructor.
  - by constructor.
  - move: Hp' => /reaches_terminating H /H ?. by left.
  - move: Hp' => /reaches_non_terminating H /H ?. by right.
Qed.

Print Assumptions decider.
