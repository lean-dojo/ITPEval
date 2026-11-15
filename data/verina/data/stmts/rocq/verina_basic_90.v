(* Statement-only formalization of VERINA corpus artifact verina_basic_90,
   catalog title "SlopeSearch": executable fuel-bounded slope search for an
   integer in a nonempty rectangular matrix sorted by rows and columns,
   together with its precondition, found-or-absent postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Module VerinaBasic90.

Definition get2d
    (a : list (list Z))
    (i j : Z) : Z :=
  nth (Z.to_nat j)
    (nth (Z.to_nat i) a [])
    0.

Fixpoint SlopeSearch_pairwise
    {A : Type}
    (relation : A -> A -> Prop)
    (xs : list A) : Prop :=
  match xs with
  | [] => True
  | x :: rest =>
      Forall (relation x) rest /\
      SlopeSearch_pairwise relation rest
  end.

Definition SlopeSearch_precond
    (a : list (list Z))
    (_key : Z) : Prop :=
  (0 < length a)%nat /\
  (0 < length (nth 0 a []))%nat /\
  SlopeSearch_pairwise
    (fun row1 row2 => length row1 = length row2)
    a /\
  Forall (SlopeSearch_pairwise Z.le) a /\
  forall i : nat,
    (i < length (nth 0 a []))%nat ->
    SlopeSearch_pairwise
      Z.le
      (map (fun row => nth i row 0) a).

Fixpoint SlopeSearch_aux
    (a : list (list Z))
    (key : Z)
    (rows : nat)
    (m n : Z)
    (fuel : nat) : Z * Z :=
  match fuel with
  | O => (-1, -1)
  | S fuel' =>
      if orb
          (Z.geb m (Z.of_nat rows))
          (Z.ltb n 0)
      then (-1, -1)
      else if Z.eqb (get2d a m n) key
      then (m, n)
      else if Z.ltb (get2d a m n) key
      then SlopeSearch_aux a key rows (m + 1) n fuel'
      else SlopeSearch_aux a key rows m (n - 1) fuel'
  end.

Definition SlopeSearch
    (a : list (list Z))
    (key : Z)
    (_h_precond : SlopeSearch_precond a key) : Z * Z :=
  let rows := length a in
  let cols :=
    if Nat.ltb 0 rows
    then length (nth 0 a [])
    else 0%nat in
  SlopeSearch_aux
    a key rows 0
    (Z.of_nat (cols - 1))
    (rows + cols).

Definition SlopeSearch_postcond
    (a : list (list Z))
    (key : Z)
    (result : Z * Z)
    (_h_precond : SlopeSearch_precond a key) : Prop :=
  let '(m, n) := result in
  (m >= 0 /\
   m < Z.of_nat (length a) /\
   n >= 0 /\
   n < Z.of_nat (length (nth 0 a [])) /\
   get2d a m n = key) \/
  (m = -1 /\
   n = -1 /\
   Forall
     (fun row => Forall (fun element => element <> key) row)
     a).

Theorem SlopeSearch_spec_satisfied
    (a : list (list Z))
    (key : Z)
    (h_precond : SlopeSearch_precond a key) :
  SlopeSearch_postcond
    a key (SlopeSearch a key h_precond) h_precond.
Admitted.

End VerinaBasic90.
