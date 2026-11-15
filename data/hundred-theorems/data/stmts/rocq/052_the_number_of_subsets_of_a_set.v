From mathcomp Require Import all_ssreflect.

(**
  The powerset of a finite set has cardinality two raised to the cardinality
  of the original set.
*)
Theorem number_of_subsets (T : finType) (A : {set T}) :
  #|powerset A| = 2 ^ #|A|.
Proof.
  exact: card_powerset.
Qed.
