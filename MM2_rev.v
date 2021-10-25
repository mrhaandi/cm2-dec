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

Lemma multi_step_ubound {k p a b p' a' b'} : multi_step k (p, (a, b)) = Some (p', (a', b')) -> a' <= k + a /\ b' <= k + b.
Proof.
Admitted.

Lemma iter_None {X : Type} (f : X -> option X) k : Nat.iter k (option_bind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

Lemma option_bind_iter {X : Type} (f : X -> option X) k x : 
  option_bind f (Nat.iter k (option_bind f) (Some x)) = Nat.iter k (option_bind f) (f x).
Proof. elim: k; [done|by move=> k /= ->]. Qed.

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

(* terminate or reach uniformly next config or reach small config *)
Corollary next_waypoint_b p b :
  terminating (p, (0, b)) \/
  (exists p' b', forall n, reaches_plus (p, (0, n+b)) (p', (0, n+b'))) \/
  exists p' a' b', reaches (p, (0, b)) (p', (a', b')) /\ a' <= l + 1 /\ b' <= l + 1.
Proof.
  have [?|?] : b <= l + 1 \/ b > l + 1 by lia.
  { do 2 right. exists p, 0, b. split; [by exists 0 | lia]. }
  have [k [? Hk]] := next_waypoint p 0 b.
  move: Hk. case E: (multi_step k (p, (0, b))) => [[p' [a' b']]|]; first last.
  { move=> _. left. by exists k. }
  move=> [?|[?|?]]; right.
  - right. exists p', a', b'. split; [|lia]. by exists k.
  - move: E => /parallel_b => /(_ ltac:(lia)) [].
    + move=> [k' [p'' [a'' [?]]]] Hk'.
      move: (Hk') => /multi_step_ubound ?. right.
      exists p'', a'', 0. split; last by lia.
      by exists k'.
    + move=> H. left. exists p', b' => n. exists k. split; first by lia.
      rewrite (H n). congr (Some (p', (_, n + b'))). lia.
  - right. exists p', a', 0.
    move: (E) => /multi_step_ubound ?.
    split; last by lia.
    exists k. rewrite E. congr (Some (p', (a', _))). lia.
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

Lemma reaches_non_terminating {x y} : reaches x y -> non_terminating y -> non_terminating x.
Proof.
  move=> [k Hk] Hy k' Hk'.
Admitted.

Lemma reaches_trans {x y z} : reaches x y -> reaches y z -> reaches x z.
Proof. Admitted.

Lemma big p b p' b' (L : list (nat*nat)) :
  0 < length L -> 
  NoDup (map fst L) ->
  Forall (fun '(p'', b'') => forall n, reaches (p, (0, n+b)) (p'', (0, n+b''))) L ->
  Forall (fun '(p'', b'') => forall n, reaches (p'', (0, n+b'')) (p', (0, n+b'))) L -> 
  terminating (p, (0, b)) \/
  non_terminating (p, (0, b)) \/
  (exists p'' a'' b'', reaches (p, (0, b)) (p'', (a'', b'')) /\ a'' <= l + 1 /\ b'' <= l + 1).
Proof.
  move Hn: ((l+l+3) - length L) => n.
  elim: n L Hn p' b'.
  { move=> L ? p' b' _ H1L. move: (H1L) => /NoDup_incl_length H H2L.
    pose L' := map (fun '(p'', b'') => (p'', (0, b''))) L.
    suff : length L' <= l+l+2 by (rewrite /L' map_length; lia).
    apply /(distinct_states (p, (0, b))).
    - rewrite /L' Forall_mapP. apply: Forall_impl H2L.
      by move=> [p'' b''] /(_ 0).
    - rewrite /L' map_map. move: H1L. congr NoDup.
      by apply /map_ext => - [? ?]. }
  move=> k IH L ? p' b' H0L H1L H2L H3L.
  have H : forall n, reaches (p, (0, n+b)) (p', (0, n+b')).
  { move: H0L H2L H3L. clear. case: L => /=; first by lia.
    move=> [p'' b''] ? _ /ForallE [H1 _] /ForallE [H2 _] n.
    exact: (reaches_trans (H1 n) (H2 n)). }
  have [H1|[[p'' [b'' H2]]|[p'' [a'' [b'' [H3 ?]]]]]] := next_waypoint_b p' b'.
  - left. exact: (reaches_terminating (H 0) H1).
  - have [|Hp''] := In_dec Nat.eq_dec p'' (map fst L).
    + (* state visited *)
      move=> /in_map_iff [[p''' b'''] /= [?]] H4L. subst p'''.
      move: H2L (H4L) => /Forall_forall H' /H'{H'} H2L.
      move: H3L (H4L) => /Forall_forall H' /H'{H'} H3L.
      have [?|?] : b''' <= b'' \/ b'' < b''' by lia.
      * right. left. apply: (reaches_non_terminating (H 0)).
        apply: (reaches_non_terminating (reaches_plus_incl (H2 0))).
        have H' : forall n, reaches_plus (p'', (0, n + b''')) (p'', (0, n + b'')).
        { move=> n. exact: (reaches_reaches_plus (H3L n) (H2 n)). }
        move=> k'. admit. (* doable via loop *)
      * do 2 right. exists p'', 0. (* HOW TO GO DOWN? *)
    + (* state not visited *)
      have := IH ((p'', b'') :: L).
      move=> /= /(_ ltac:(lia) p'' b''). apply.
      * lia.
      * by constructor.
      * constructor; last done.
        move=> n. exact: (reaches_trans (H n) (reaches_plus_incl (H2 n))).
      * constructor.
        { move=> n. by exists 0. }
        apply: Forall_impl H3L => - [p''' b'''] H' n.
        exact: (reaches_trans (H' n) (reaches_plus_incl (H2 n))).
  - do 2 right. exists p'', a'', b''. split; last done.
    exact: (reaches_trans (H 0) H3).
Admitted.

(* not enough 
Lemma big p b p' b' (L : list (nat*nat)) :
  (forall n, reaches_plus (p, (0, n+b)) (p', (0, n+b'))) ->
  NoDup (map fst L) ->
  Forall (fun '(p'', b'') => forall n, reaches (p, (0, n+b)) (p'', (0, n+b''))) L -> 
  terminating (p, (0, b)) \/
  non_terminating (p, (0, b)) \/
  (exists p'' a'' b'', reaches_plus (p, (0, b)) (p'', (a'', b'')) /\ a'' <= l + 1 /\ b'' <= l + 1).
Proof.
  move Hn: ((l+l+3) - length L) => n.
  elim: n L Hn p' b'.
  { move=> L ? p' b' ? H1L. move: (H1L) => /NoDup_incl_length H H2L.
    pose L' := map (fun '(p'', b'') => (p'', (0, b''))) L.
    suff : length L' <= l+l+2 by (rewrite /L' map_length; lia).
    apply /(distinct_states (p, (0, b))).
    - rewrite /L' Forall_mapP. apply: Forall_impl H2L.
      by move=> [p'' b''] /(_ 0).
    - rewrite /L' map_map. move: H1L. congr NoDup.
      by apply /map_ext => - [? ?]. }
  move=> k IH L ? p' b' H H1L H2L.
  have [H1|[[p'' [b'' H2]]|[p'' [a'' [b'' [H3 ?]]]]]] := next_waypoint_b p' b'.
  - left. exact: (reaches_terminating (reaches_plus_incl (H 0)) H1).  (* easy *)
  - have [|Hp''] := In_dec Nat.eq_dec p'' (map fst L).
    + (* state visited *)
      move=> /in_map_iff [[p''' b'''] /= [?]]. subst p'''.
      move: H2L => /Forall_forall H' /H'{H'}.
    + (* state not visited *)
      have := IH ((p'', b'') :: L).
      move=> /= /(_ ltac:(lia) p'' b''). apply.
      * move=> n. exact: (reaches_plus_reaches (H n) (reaches_plus_incl (H2 n))).
      * by constructor.
      * constructor; last done.
        move=> n. exact: (reaches_plus_incl (reaches_plus_reaches (H n) (reaches_plus_incl (H2 n)))).
  - do 2 right. exists p'', a'', b''. split; last done.
    exact: (reaches_plus_reaches (H 0) H3).
Admitted.
*)