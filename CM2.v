(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Problem(s):
    Reversible Two Counter Machine Halting (CM2_REV_HALT)
    Two Counter Machine Uniform Mortality (CM2_UMORTAL)
    Two Counter Machine Uniform Boundedness (CM2_UBOUNDED)
*)

Require Import List.

(* a configuration consists of a state and two counter values *)
Definition Config : Set := nat * (nat * nat).

(* accessors for state, value1, value2 of configurations *)
Definition state (x: Config) : nat := fst x.
Arguments state !x /.
Definition value1 (x: Config) : nat := fst (snd x).
Arguments value1 !x /.
Definition value2 (x: Config) : nat := snd (snd x).
Arguments value2 !x /.

(* the instruction inc true maps 
      a configuration (p, (v1, v2)) to (1+p, (v1, 1+v2))
    the instruction inc false maps 
      a configuration (p, (v1, v2)) (1+p, (1+v1, v2))
    an instruction dec true q maps
      a configuration (p, (v1, 0)) to (1+p, (v1, 0)) 
      a configuration (p, (v1, 1+v2)) to (q, (v1, v2)) 
    an instruction dec false q maps
      a configuration (p, (0, v2)) to (1+p, (0, v2)) 
      a configuration (p, (1+v1, v2)) to (q, (v1, v2)) *)
Inductive Instruction : Set := 
  | inc : bool -> Instruction
  | dec : bool -> nat -> Instruction.

(* a two counter machine is a list of instructions *)
Definition Cm2 : Set := list Instruction.

(* partial two counter machine step function *)
Definition step (M: Cm2) (x: Config) : option Config :=
  match nth_error M (state x) with
  | None => None (* halting configuration *)
  | Some (inc b) => (* increase counter, goto next state*)
    Some (1 + (state x), ((if b then 0 else 1) + (value1 x), (if b then 1 else 0) + (value2 x)))
  | Some (dec b y) => (* decrease counter, if successful goto state y *)
    if b then 
      match value2 x with
      | 0 => Some (1 + (state x), (value1 x, 0))
      | S n => Some (y, (value1 x, n))
      end
    else
      match value1 x with
      | 0 => Some (1 + (state x), (0, value2 x))
      | S n => Some (y, (n, value2 x))
      end
  end.

Definition option_bind {X Y : Type} (f : X -> option Y) (oX : option X) : option Y :=
  match oX with None => None | Some x => f x end.

Definition multi_step (M: Cm2) (k: nat) (x: Config) : option Config :=
  Nat.iter k (option_bind (step M)) (Some x).

Definition reaches (M: Cm2) (x y: Config) := exists k, multi_step M k x = Some y.

(* does M eventually terminate starting from the configuration x? *)
Definition terminating (M: Cm2) (x: Config) :=
  exists n, multi_step M n x = None.

(* injectivity of the step function *)
Definition reversible (M : Cm2) : Prop := 
  forall x y z, step M x = Some z -> step M y = Some z -> x = y.

(* bound for the number of reachable configurations *)
Definition bounded (k: nat) (M: Cm2) (x: Config) : Prop := 
  exists (L: list Config), (length L <= k) /\ (forall (y: Config), reaches M x y -> In y L).

(* Reversible Two-counter Machine Halting Problem
   Given a reversible two-counter machine M and a configucation c, 
   does a run in M starting from c eventually terminate? *)
Definition CM2_REV_HALT : { M: Cm2 | reversible M } * Config -> Prop :=
  fun '((exist _ M _), c) => terminating M c.

Definition CM2_UMORTAL : Cm2 -> Prop :=
  fun M => exists k, forall (x: Config), multi_step M k x = None.

Definition CM2_UBOUNDED : Cm2 -> Prop :=
  fun M => exists k, forall x, bounded k M x.
