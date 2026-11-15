(* Statement-only formalization of VERINA corpus artifact verina_basic_45,
   catalog title "findProduct": an executable search for the first even and
   first odd integers in a list and the product of those entries, together
   with its parity-existence precondition, exact postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition isEven (n : Z) : bool :=
  Z.eqb (Z.modulo n 2) 0.

Definition isOdd (n : Z) : bool :=
  negb (Z.eqb (Z.modulo n 2) 0).

Fixpoint findProduct_findIdxFrom
    (predicate : Z -> bool)
    (lst : list Z)
    (i : nat) : option nat :=
  match lst with
  | [] => None
  | x :: xs =>
      if predicate x
      then Some i
      else findProduct_findIdxFrom predicate xs (S i)
  end.

Definition findProduct_findIdx
    (predicate : Z -> bool)
    (lst : list Z) : option nat :=
  findProduct_findIdxFrom predicate lst 0%nat.

Definition firstEvenOddIndices
    (lst : list Z) : option (nat * nat) :=
  let evenIndex := findProduct_findIdx isEven lst in
  let oddIndex := findProduct_findIdx isOdd lst in
  match evenIndex, oddIndex with
  | Some ei, Some oi => Some (ei, oi)
  | _, _ => None
  end.

Definition findProduct_precond
    (lst : list Z) : Prop :=
  (1 < length lst)%nat /\
  (exists x : Z, In x lst /\ isEven x = true) /\
  (exists x : Z, In x lst /\ isOdd x = true).

Definition findProduct
    (lst : list Z)
    (_h_precond : findProduct_precond lst) : Z :=
  match firstEvenOddIndices lst with
  | Some (ei, oi) => nth ei lst 0 * nth oi lst 0
  | None => 0
  end.

Definition findProduct_postcond
    (lst : list Z)
    (result : Z)
    (_h_precond : findProduct_precond lst) : Prop :=
  match firstEvenOddIndices lst with
  | Some (ei, oi) => result = nth ei lst 0 * nth oi lst 0
  | None => True
  end.

Theorem findProduct_spec_satisfied
    (lst : list Z)
    (h_precond : findProduct_precond lst) :
  findProduct_postcond
    lst (findProduct lst h_precond) h_precond.
Admitted.
