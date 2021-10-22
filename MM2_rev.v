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

Section DECIDRE.

Variable M : Mm2.

Notation step := (MM2.step M).
Notation multi_step := (MM2.multi_step M).
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
