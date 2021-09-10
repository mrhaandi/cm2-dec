Require Import List PeanoNat Lia Operators_Properties.
Import ListNotations.
Require Import ssreflect.
Require Import CM2.MM2.



Definition reversible (M : list mm2_instr) : Prop := 
  forall x y z, mm2_step M x z -> mm2_step M y z -> x = y.

(* an avid instruction may jump to a valid state (except the first) *)
Definition avid (l : nat) (i : mm2_instr) :=
  exists p, S p < l /\ (i = mm2_dec_a (S (S p)) \/ i = mm2_dec_b (S (S p))).

Lemma mm2_instr_at_nth (M : list mm2_instr) p i : p < length M -> mm2_instr_at (nth p M i) (S p) M.
Proof.
  elim: M p; cbn; [lia|].
  move=> j M IH [|p].
  - move=> _. by exists [], M.
  - move=> ?. move: (IH p ltac:(lia)) => [Ml] [Mr] [HM <-].
    exists (j :: Ml), Mr. constructor; cbn; [|lia].
    congr cons. assumption.
Qed.

Lemma mm2_instr_at_nth' (M : list mm2_instr) p i j : p < length M -> nth p M i = j -> mm2_instr_at j (S p) M.
Proof. move=> ? <-. by apply: mm2_instr_at_nth. Qed.

(* a reversible machine has no avid instruction *)
Lemma reversible_not_avid (M : list mm2_instr) :
  reversible M -> Forall (fun i => not (avid (length M) i)) M.
Proof.
  move=> HM. apply /Forall_Exists_neg => /Exists_nth [p] [i] [Hp] [q] [?] H'p.
  move H'q: (nth q M i) => iq. have Hq: (q < length M) by lia. case: iq H'q.
  - move=> H'q. case: H'p => [H'p|H'p].
    + suff: (S p, (2, 0)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(1,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
    + suff: (S p, (1, 1)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(1,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
  - move=> H'q. case: H'p => [H'p|H'p].
    + suff: (S p, (1, 1)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,1))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
    + suff: (S p, (0, 2)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,1))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
  - move=> r H'q. case: H'p => [H'p|H'p].
    + suff: (S p, (1, 0)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
    + suff: (S p, (0, 1)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
  - move=> r H'q. case: H'p => [H'p|H'p].
    + suff: (S p, (1, 0)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
    + suff: (S p, (0, 1)) = (S q, (0, 0)) by done.
      apply: (HM _ _ (S (S q),(0,0))); eexists; eauto using mm2_instr_at_nth', mm2_atom.
Qed.

Arguments clos_rt_rt1n_iff {A R x y}.

Definition trunc1 n := match n with 0 => 0 | S _ => 1 end.
Definition trunc2 n := match n with 0 => 0 | 1 => 1 | S (S _) => 2 end.
Definition trunc_state l p := if (S l) - p is 0 then 0 else p.
Definition trunc_config l (x : (nat*(nat*nat))%type) :=
  match x with
  | (p, (a, b)) => (trunc_state l p,
    match p with
    | 1 => (trunc1 a, trunc1 b)
    | _ => (trunc2 a, trunc2 b)
    end)
  end.

(* truncated step function *)
Definition next M x :=
  match x with
  | (0, _) => None
  | (S p', (a, b)) =>
    match nth_error M p' with
    | None => None
    | Some (mm2_inc_a) => Some (trunc_config (length M) (S (S p'), (S a, b)))
    | Some (mm2_inc_b) => Some (trunc_config (length M) (S (S p'), (a, S b)))
    | Some (mm2_dec_a q) =>
      Some (trunc_config (length M) (if a is S a' then (q, (a', b)) else (S (S p'), (a, b))))
    | Some (mm2_dec_b q) => 
      Some (trunc_config (length M) (if b is S b' then (q, (a, b')) else (S (S p'), (a, b))))
    end
  end.

Lemma mm2_instr_at_trunc_state {i p M} : mm2_instr_at i p M -> trunc_state (length M) p = p.
Proof.
  move=> [l] [r] [->].
  move: p => [|p]; first by lia.
  rewrite app_length /trunc_state /= => - [->].
  case E: (p + S (length r) - p); lia.
Qed.

Lemma mm2_instr_at_nth_error {i p M} : mm2_instr_at i (S p) M -> nth_error M p = Some i.
Proof.
  elim: M p.
  - by move=> ? [[|? l]] [r] [H].
  - move=> j M IH p [[|j' l]] [r] /=.
    + by move=> [[->]] _ [<-].
    + move=> [[]] _ ? [<-]. apply: IH.
      by exists l, r.
Qed.

Lemma asd M x y : mm2_step M x y -> next M (trunc_config (length M) x) = Some (trunc_config (length M) y).
Proof.
  move=> [] i [Hi] H. move: H Hi => [] /=.
  - move=> {}p a b Hp. rewrite (mm2_instr_at_trunc_state Hp).
    move: p Hp => [|p] Hp. admit. (* easy*)
    rewrite (mm2_instr_at_nth_error Hp).
    clear Hp. move: p => [|p].
    destruct a; cbn. admit. admit. (* issue *)
    destruct a. cbn. admit.
    cbn. destruct a; cbn.
    congr Some. congr pair.
    cbn.
  
  /mm2_instr_at_trunc_state ->.
(*
Definition trunc1_config (s : (nat*(nat*nat))%type) := 
  match s with (p,(a, b)) => (p, (trunc1 a, trunc1 b)) end.

Definition trunc2_config (s : (nat*(nat*nat))%type) := 
  match s with (p,(a, b)) => (p, (trunc2 a, trunc2 b)) end.

Lemma trunc1_trunc2 n : trunc1 (trunc2 n) = trunc1 n.
Proof. by move: n => [|[|n]]. Qed.
*)
(* trunc config step by step *)
Lemma asd M x y : mm2_step M x y -> fst y = 1 ->
  exists a b, mm2_step M (trunc2_config x) (1, (a, b)) /\ trunc1_config y = trunc1_config (1, (a, b)).
Proof.
  move=> [] [] [].
  - move=> H H'. move: H' H => []; cbn.
    + move=> p a b [?] [?] []. lia.
    + move=> p a b [?] [?] []. lia.
    + move=> p q a b Hp ?. subst q.
      move: a => [|a].
      * exists 0, (trunc2 b). constructor; last by rewrite trunc1_trunc2.
        eexists. constructor; [exact: Hp|]. eauto using mm2_atom.
      * exists 1, (trunc2 b). constructor; last by rewrite trunc1_trunc2.
        eexists. constructor; [exact: Hp|]. eauto using mm2_atom.
    + admit.
    + move=> p q b [?] [?] []. lia.
    + move=> p q a [?] [?] []. lia.
  

    move: Hp => [?] [?] []. lia.
    
    case: Hp.
  
  move: x => [p ?] ? [].

Lemma asd M x a b : mm2_step M x (0, (a, b)) -> 
  exists a' b', mm2_step M (trunc2_config x) (0, (a', b')) /\ trunc1_config (0, (a, b)) = trunc1_config (0, (a', b')).
Proof.
  move=> [].

Definition truc1 (s : (nat*(nat*nat))%type) := match s with 
  | (p,(0, 0)) => (p, (0, 0))
  | (p, (S a, 0)) => (p, (1, 0))
  | (p, (0, S b)) => (p, (0, 1))


Lemma key M s : mm2_terminates M s -> forall p a b, 
  (s = (0, (S a, b)) -> mm2_terminates M (0, (1, b))) /\
  (s = (0, (a, S b)) -> mm2_terminates M (0, (a, 1))) /\
  (s = (p, (S (S a), b)) -> mm2_terminates M (0, (2, b))) /\
  (s = (p, (a, S (S b))) -> mm2_terminates M (0, (a, 2))).
Proof.
  move=> [t] [/clos_rt_rt1n_iff]. elim.
  - move=> {}s. admit. (* easy*)
  - move=> {}s s' {}t [] [].
    + move=> [? []]. _ IH /IH {}IH p a b. do ? split.
      * 
  -