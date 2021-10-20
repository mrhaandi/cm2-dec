(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Result(s):
    Decidability of Reversible Two Counter Machine Halting (CM2_REV_HALT_dec)
*)

Require Import CM2.CM2 CM2.CM2_rev.

Theorem CM2_REV_HALT_dec :
  exists f : { M: Cm2 | reversible M } * Config -> bool,
  forall X, f X = true <-> CM2_REV_HALT X.
Proof.
  exists (fun '((exist _ M HM), c) => decider M HM c).
  intros [[M HM] c]. exact (decider_spec M HM c).
Qed.