(* Statement-only formalization of VERINA corpus artifact verina_advanced_11,
   catalog title "findMajorityElement": an executable first-match search for
   an integer occurring strictly more than half the time, with -1 as the
   fallback and the associated correctness contract. This file contains no
   proof. *)

From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition findMajorityElement_precond (lst : list Z) : Prop :=
  True.

Definition countOccurrences (n : Z) (lst : list Z) : nat :=
  fold_left
    (fun acc x =>
      if Z.eq_dec x n then S acc else acc)
    lst 0%nat.

Fixpoint findMajorityElement_find
    (lst remaining : list Z) : option Z :=
  match remaining with
  | [] => None
  | x :: xs =>
      if Nat.ltb
           (Nat.div (length lst) 2)
           (countOccurrences x lst)
      then Some x
      else findMajorityElement_find lst xs
  end.

Definition findMajorityElement
    (lst : list Z)
    (_h_precond : findMajorityElement_precond lst) : Z :=
  match findMajorityElement_find lst lst with
  | Some x => x
  | None => -1
  end.

Definition findMajorityElement_count
    (x : Z) (lst : list Z) : nat :=
  length (filter (fun y => Z.eqb y x) lst).

Definition findMajorityElement_majority
    (lst : list Z) (result : Z) : Prop :=
  (Nat.div (length lst) 2 <
     findMajorityElement_count result lst)%nat /\
  forallb
    (fun x =>
      orb
        (Nat.leb
          (findMajorityElement_count x lst)
          (Nat.div (length lst) 2))
        (Z.eqb x result))
    lst = true.

Definition findMajorityElement_postcond
    (lst : list Z)
    (result : Z)
    (_h_precond : findMajorityElement_precond lst) : Prop :=
  (result = -1 ->
    forallb
      (fun x =>
        Nat.leb
          (findMajorityElement_count x lst)
          (Nat.div (length lst) 2))
      lst = true \/
    findMajorityElement_majority lst result) /\
  (result <> -1 ->
    findMajorityElement_majority lst result).

Theorem findMajorityElement_spec_satisfied
    (lst : list Z)
    (h_precond : findMajorityElement_precond lst) :
  findMajorityElement_postcond
    lst (findMajorityElement lst h_precond) h_precond.
Admitted.
