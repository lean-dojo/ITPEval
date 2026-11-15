(* This statement uses MathComp's algebra, matrix, and polynomial libraries. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple finfun bigop fingroup perm.
From mathcomp Require Import nmodule algebra divalg decfield matrix mxalgebra.
From mathcomp Require Import poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(**
  Cayley-Hamilton: evaluating a square matrix's characteristic polynomial at
  that matrix gives the zero matrix.
*)
Theorem Cayley_Hamilton (R : comNzRingType) n' (A : 'M[R]_n'.+1) :
  horner_mx A (char_poly A) = 0.
Proof.
Admitted.
