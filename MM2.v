(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Problem(s):
    Two-Counter Minsky Machine Halting (MM2_HALT)
*)

Require Import List ssrfun.

(* a configuration consists of a state and two counter values *)
Definition Config : Set := nat * (nat * nat).

(* accessors for state, value1, value2 of configurations *)
Definition state (x: Config) : nat := fst x.
Arguments state !x /.
Definition value1 (x: Config) : nat := fst (snd x).
Arguments value1 !x /.
Definition value2 (x: Config) : nat := snd (snd x).
Arguments value2 !x /.

(* the instruction zero true maps 
      a configuration (p, (v1, v2)) to (1+p, (v1, 0))
    the instruction zero false maps 
      a configuration (p, (v1, v2)) (1+p, (0, v2))
    the instruction inc true maps 
      a configuration (p, (v1, v2)) to (1+p, (v1, 1+v2))
    the instruction inc false maps 
      a configuration (p, (v1, v2)) (1+p, (1+v1, v2))
    an instruction dec true q maps
      a configuration (p, (v1, 0)) to (q, (v1, 0)) 
      a configuration (p, (v1, 1+v2)) to (1+p, (v1, v2)) 
    an instruction dec false q maps
      a configuration (p, (0, v2)) to (q, (0, v2)) 
      a configuration (p, (1+v1, v2)) to (1+p, (v1, v2)) *)
Inductive Instruction : Set :=
  | halt : Instruction
  | zero : bool -> Instruction
  | inc : bool -> Instruction
  | dec : bool -> nat -> Instruction.

(* a two counter machine is a list of instructions *)
Definition Mm2 : Set := list Instruction.

(* partial two counter Minsky machine step function *)
Definition step (M: Mm2) (x: Config) : option Config :=
  match nth_error M (state x) with
  | None => None (* halting configuration *)
  | Some halt => None (* halting instruction *)
  | Some (zero b) => (* set counter to zero, goto next state*)
    Some (1 + (state x), ((if b then (value1 x) else 0), (if b then 0 else (value2 x))))
  | Some (inc b) => (* increase counter, goto next state*)
    Some (1 + (state x), ((if b then 0 else 1) + (value1 x), (if b then 1 else 0) + (value2 x)))
  | Some (dec b y) => (* decrease counter, if successful goto state y *)
    if b then 
      match value2 x with
      | 0 => Some (y, (value1 x, 0))
      | S n => Some (1 + (state x), (value1 x, n))
      end
    else
      match value1 x with
      | 0 => Some (y, (0, value2 x))
      | S n => Some (1 + (state x), (n, value2 x))
      end
  end.

Definition steps (M: Mm2) (n: nat) (x: Config) : option Config :=
  Nat.iter n (obind (step M)) (Some x).

(* does M eventually terminate starting from the configuration x? *)
Definition terminating (M: Mm2) (x: Config) :=
  exists n, steps M n x = None.

(* Two-counter Minsky Machine Halting Problem:
   Given a two-counter Minsky machine M and a configucation c, 
   does a run in M starting from c eventually terminate? *)
Definition MM2_HALT : Mm2 * Config -> Prop :=
  fun '(M, c) => terminating M c.
