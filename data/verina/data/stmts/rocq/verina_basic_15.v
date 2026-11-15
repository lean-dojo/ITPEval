(* Statement-only formalization of VERINA corpus artifact verina_basic_15,
   catalog title "containsConsecutiveNumbers": executable Boolean detection
   of an adjacent integer pair whose second element is one greater than its
   first, together with its no-precondition correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition containsConsecutiveNumbers_precond (_a : list Z) : Prop :=
  True.

Fixpoint containsConsecutiveNumbers_scan
    (previous : Z)
    (rest : list Z) : bool :=
  match rest with
  | [] => false
  | current :: tail =>
      if Z.eqb (previous + 1) current
      then true
      else containsConsecutiveNumbers_scan current tail
  end.

Definition containsConsecutiveNumbers
    (a : list Z)
    (_h_precond : containsConsecutiveNumbers_precond a) : bool :=
  match a with
  | [] => false
  | first :: rest => containsConsecutiveNumbers_scan first rest
  end.

Definition containsConsecutiveNumbers_postcond
    (a : list Z)
    (result : bool)
    (_h_precond : containsConsecutiveNumbers_precond a) : Prop :=
  (exists i : nat,
      (i < length a - 1)%nat /\
      nth i a 0%Z + 1 = nth (S i) a 0%Z) <->
  result = true.

Theorem containsConsecutiveNumbers_spec_satisfied
    (a : list Z)
    (h_precond : containsConsecutiveNumbers_precond a) :
  containsConsecutiveNumbers_postcond
    a (containsConsecutiveNumbers a h_precond) h_precond.
Admitted.
