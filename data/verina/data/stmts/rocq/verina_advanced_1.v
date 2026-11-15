(* Statement-only formalization of VERINA corpus artifact verina_advanced_1,
   catalog title "FindSingleNumber": an executable list scan that returns the
   unique integer occurring once when all others occur twice. This file
   contains no proof. *)

From Stdlib Require Import List ZArith.

Import ListNotations.
Open Scope Z_scope.

Fixpoint filterlist (x : Z) (nums : list Z) : list Z :=
  match nums with
  | [] => []
  | y :: ys =>
      if Z.eq_dec y x
      then y :: filterlist x ys
      else filterlist x ys
  end.

Definition FindSingleNumber_precond (nums : list Z) : Prop :=
  let numsCount :=
    map (fun x : Z => count_occ Z.eq_dec nums x) nums in
  forallb
    (fun count : nat =>
      orb (Nat.eqb count 1) (Nat.eqb count 2))
    numsCount = true /\
  count_occ Nat.eq_dec numsCount 1%nat = 1%nat.

Fixpoint FindSingleNumber_findUnique
    (nums remaining : list Z) : Z :=
  match remaining with
  | [] => 0
  | x :: xs =>
      let filtered := filterlist x nums in
      let count := length filtered in
      if Nat.eqb count 1
      then x
      else FindSingleNumber_findUnique nums xs
  end.

Definition FindSingleNumber
    (nums : list Z)
    (_h_precond : FindSingleNumber_precond nums) : Z :=
  FindSingleNumber_findUnique nums nums.

Definition FindSingleNumber_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : FindSingleNumber_precond nums) : Prop :=
  (0 < length nums)%nat /\
  length (filterlist result nums) = 1%nat /\
  forall x : Z,
    In x nums ->
    x = result \/ length (filterlist x nums) = 2%nat.

Theorem FindSingleNumber_spec_satisfied
    (nums : list Z)
    (h_precond : FindSingleNumber_precond nums) :
  FindSingleNumber_postcond
    nums (FindSingleNumber nums h_precond) h_precond.
Admitted.
