(* Statement-only formalization of VERINA corpus artifact verina_basic_78,
   catalog title "MultipleReturns": executable computation returning the sum
   and difference of two arbitrary integers as a pair, together with its
   trivial precondition, postcondition, and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition MultipleReturns_precond (_x _y : Z) : Prop :=
  True.

Definition MultipleReturns
    (x y : Z)
    (_h_precond : MultipleReturns_precond x y) : Z * Z :=
  let more := x + y in
  let less := x - y in
  (more, less).

Definition MultipleReturns_postcond
    (x y : Z)
    (result : Z * Z)
    (_h_precond : MultipleReturns_precond x y) : Prop :=
  fst result = x + y /\
  snd result + y = x.

Theorem MultipleReturns_spec_satisfied
    (x y : Z)
    (h_precond : MultipleReturns_precond x y) :
  MultipleReturns_postcond
    x y (MultipleReturns x y h_precond) h_precond.
Admitted.
