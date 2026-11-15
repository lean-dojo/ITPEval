(* Statement-only formalization of VERINA corpus artifact verina_advanced_24,
   catalog title "lengthOfLIS": an executable patience-sorting computation of
   the longest strictly increasing subsequence length of an integer list,
   together with its exhaustive-subsequence correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition lengthOfLIS_precond (_nums : list Z) : Prop :=
  True.

Fixpoint lengthOfLIS_replace
    (x : Z) (l acc : list Z) : list Z :=
  match l with
  | [] => rev acc ++ [x]
  | y :: ys =>
      if Z.leb x y
      then rev acc ++ (x :: ys)
      else lengthOfLIS_replace x ys (y :: acc)
  end.

Definition lengthOfLIS_lisHelper
    (dp : list Z) (x : Z) : list Z :=
  lengthOfLIS_replace x dp [].

Definition lengthOfLIS
    (nums : list Z)
    (_h_precond : lengthOfLIS_precond nums) : Z :=
  Z.of_nat (length (fold_left lengthOfLIS_lisHelper nums [])).

Fixpoint lengthOfLIS_isStrictlyIncreasing
    (l : list Z) : bool :=
  match l with
  | [] => true
  | _ :: [] => true
  | x :: (y :: rest as tail) =>
      andb
        (Z.ltb x y)
        (lengthOfLIS_isStrictlyIncreasing tail)
  end.

Fixpoint lengthOfLIS_subsequences
    (xs : list Z) : list (list Z) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
      let rest := lengthOfLIS_subsequences xs' in
      rest ++ map (fun r => x :: r) rest
  end.

Definition lengthOfLIS_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : lengthOfLIS_precond nums) : Prop :=
  let allIncreasing :=
    filter
      lengthOfLIS_isStrictlyIncreasing
      (lengthOfLIS_subsequences nums) in
  existsb
    (fun l => Z.eqb (Z.of_nat (length l)) result)
    allIncreasing = true /\
  forallb
    (fun l => Z.leb (Z.of_nat (length l)) result)
    allIncreasing = true.

Theorem lengthOfLIS_spec_satisfied
    (nums : list Z)
    (h_precond : lengthOfLIS_precond nums) :
  lengthOfLIS_postcond
    nums (lengthOfLIS nums h_precond) h_precond.
Admitted.
