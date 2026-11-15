(* Statement-only formalization of VERINA corpus artifact verina_basic_59,
   catalog title "DoubleQuadruple": an executable integer computation whose
   first result is twice the input and whose second result is twice the first,
   together with its correctness contract. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition DoubleQuadruple_precond (_x : Z) : Prop :=
  True.

Definition DoubleQuadruple
    (x : Z)
    (_h_precond : DoubleQuadruple_precond x) : (Z * Z)%type :=
  let a := 2 * x in
  let b := 2 * a in
  (a, b).

Definition DoubleQuadruple_postcond
    (x : Z)
    (result : (Z * Z)%type)
    (_h_precond : DoubleQuadruple_precond x) : Prop :=
  fst result = 2 * x /\
  snd result = 2 * fst result.

Theorem DoubleQuadruple_spec_satisfied
    (x : Z)
    (h_precond : DoubleQuadruple_precond x) :
  DoubleQuadruple_postcond
    x (DoubleQuadruple x h_precond) h_precond.
Admitted.
