(* Statement-only formalization of VERINA corpus artifact verina_basic_92,
   catalog title "SwapArithmetic": executable swapping of two arbitrary
   integers by subtraction and addition, together with its unconditional
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition SwapArithmetic_precond (_X _Y : Z) : Prop :=
  True.

Definition SwapArithmetic
    (X Y : Z)
    (_h_precond : SwapArithmetic_precond X Y) : (Z * Z)%type :=
  let x1 := X in
  let y1 := Y in
  let x2 := y1 - x1 in
  let y2 := y1 - x2 in
  let x3 := y2 + x2 in
  (x3, y2).

Definition SwapArithmetic_postcond
    (X Y : Z)
    (result : (Z * Z)%type)
    (_h_precond : SwapArithmetic_precond X Y) : Prop :=
  fst result = Y /\
  snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y).

Theorem SwapArithmetic_spec_satisfied
    (X Y : Z)
    (h_precond : SwapArithmetic_precond X Y) :
  SwapArithmetic_postcond
    X Y (SwapArithmetic X Y h_precond) h_precond.
Admitted.
