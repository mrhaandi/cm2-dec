(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Result(s):
    Decidability of Two Counter Minsky Machine Halting (MM2_HALT_dec)
    Decidability of Reversible Two Counter Machine Halting (CM2_REV_HALT_dec)
*)

Require M2.CM2 M2.CM2_REV_HALT_dec.
Require M2.MM2 M2.MM2_HALT_dec.

(* (reflects b P) means that 
   provability of the proposition P coincides with b being true *)
Definition reflects (b : bool) (P : Prop) := P <-> b = true.

(* (decidable P) means that
  there exists a (total, computable, Boolean) decider f of P *)
Definition decidable {X} (P : X -> Prop) : Prop :=
  exists f : X -> bool, forall x, reflects (f x) (P x).

(* Decidability of Two Counter Minsky Machine Halting *)
Theorem MM2_HALT_dec : decidable MM2.MM2_HALT.
Proof.
  exists (fun '(M, c) => MM2_HALT_dec.decider M c).
  intros [M c]. exact (MM2_HALT_dec.decider_spec M c).
Qed.

Check MM2_HALT_dec.
Print Assumptions MM2_HALT_dec.

(* Decidability of Reversible Two Counter Machine Halting *)
Theorem CM2_REV_HALT_dec : decidable CM2.CM2_REV_HALT.
Proof.
  exists (fun '((exist _ M HM), c) => CM2_REV_HALT_dec.decider M HM c).
  intros [[M HM] c]. exact (CM2_REV_HALT_dec.decider_spec M HM c).
Qed.

Check CM2_REV_HALT_dec.
Print Assumptions CM2_REV_HALT_dec.
