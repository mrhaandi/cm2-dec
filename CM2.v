(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Two Counter Machine Halting (CM2_HALT)
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

Definition multi_step (M: Cm2) (n: nat) (x: Config) : option Config :=
  Nat.iter n (option_bind (step M)) (Some x).

(* Does M eventually terminate starting from the configuration x ? *)
Definition terminating (M: Cm2) (x: Config) :=
  exists n, multi_step M n x = None.

(* Two Counter Machine Halting Problem
   Does a run starting from
   the configuration (state := 0, (value1 := 0, value2 := 0))
   eventually terminate? *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => terminating M (0, (0, 0)).

(*

(* halting configuration property *)
Definition halting (M : Cm2) (x: Config) : Prop := step M x = None.

Definition option_get {X : Type} (x : X) (oX : option X) : X :=
  match oX with
  | None => x
  | Some x' => x'
  end.

Require Import ssreflect ssrbool ssrfun.
Search (option _ -> _). Print oapp.
Definition option_bind {X Y : Type} (f : X -> option Y) (oX : option X) : option Y :=
  match oX with None => None | Some x => f x end.

(* total two counter machine step function
   which loops on halting configurations *)
Definition total_step (M: Cm2) (x: Config) : Config :=
  match step M x with None => x | Some y => y end.

(* Two Counter Machine Halting Problem *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => exists (n: nat), 
    halting M (Nat.iter n (fun x => option_get x (step M x))) {| state := 0; value1 := 0; value2 := 0 |}).


(* Two Counter Machine Halting Problem *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => exists (n: nat), 
    halting M (Nat.iter n (total_step M) {| state := 0; value1 := 0; value2 := 0 |}).

    
Definition option_bind {X Y : Type} (f : X -> option Y) (oX : option X) : option Y :=
  match oX with None => None | Some x => f x end.
  
(* Two Counter Machine Halting Problem
   Does a run starting from
   the configuration {| state := 0; value1 := 0; value2 := 0 |}
   eventually terminate? *)
Definition CM2_HALT : Cm2 -> Prop :=
  fun M => exists (n: nat), 
    Nat.iter n (option_bind (step M)) (Some {| state := 0; value1 := 0; value2 := 0 |}) = None.

    halting M (Nat.iter n (total_step M) {| state := 0; value1 := 0; value2 := 0 |}).*)