(* Statement-only formalization of VERINA corpus artifact verina_advanced_50,
   catalog title "mergeSorted": an executable indexed stable merge of two
   nondecreasing natural-number arrays, including its suffix-draining
   computation, together with sortedness and permutation correctness. This
   file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Sorting.Permutation
  Sorting.Sorted.

Import ListNotations.

Definition mergeSorted_precond
    (a1 a2 : list nat) : Prop :=
  StronglySorted Nat.le a1 /\
  StronglySorted Nat.le a2.

Record mergeSorted_loop_state : Type := {
  mergeSorted_i : nat;
  mergeSorted_j : nat;
  mergeSorted_result : list nat
}.

Fixpoint mergeLoop_fuel
    (fuel : nat)
    (a1 a2 : list nat)
    (i j : nat)
    (result : list nat) : mergeSorted_loop_state :=
  match fuel with
  | O =>
      {| mergeSorted_i := i;
         mergeSorted_j := j;
         mergeSorted_result := result |}
  | S fuel' =>
      if andb
          (Nat.ltb i (length a1))
          (Nat.ltb j (length a2))
      then
        let x := nth i a1 0 in
        let y := nth j a2 0 in
        if Nat.leb x y
        then
          mergeLoop_fuel
            fuel' a1 a2 (S i) j (result ++ [x])
        else
          mergeLoop_fuel
            fuel' a1 a2 i (S j) (result ++ [y])
      else
        {| mergeSorted_i := i;
           mergeSorted_j := j;
           mergeSorted_result := result |}
  end.

Definition mergeLoop
    (a1 a2 : list nat)
    (i j : nat)
    (result : list nat) : mergeSorted_loop_state :=
  mergeLoop_fuel
    (Nat.add
      (Nat.sub (length a1) i)
      (Nat.sub (length a2) j))
    a1 a2 i j result.

Fixpoint drain_fuel
    (fuel : nat)
    (arr : list nat)
    (i : nat)
    (result : list nat) : list nat :=
  match fuel with
  | O => result
  | S fuel' =>
      if Nat.ltb i (length arr)
      then
        drain_fuel
          fuel' arr (S i) (result ++ [nth i arr 0])
      else result
  end.

Definition drain
    (arr : list nat)
    (i : nat)
    (result : list nat) : list nat :=
  drain_fuel (Nat.sub (length arr) i) arr i result.

Definition mergeSorted
    (a1 a2 : list nat)
    (_h_precond : mergeSorted_precond a1 a2) : list nat :=
  let state := mergeLoop a1 a2 0 0 [] in
  let result1 :=
    drain a1
      (mergeSorted_i state)
      (mergeSorted_result state) in
  drain a2 (mergeSorted_j state) result1.

Definition mergeSorted_postcond
    (a1 a2 result : list nat)
    (_h_precond : mergeSorted_precond a1 a2) : Prop :=
  StronglySorted Nat.le result /\
  Permutation result (a1 ++ a2).

Theorem mergeSorted_spec_satisfied
    (a1 a2 : list nat)
    (h_precond : mergeSorted_precond a1 a2) :
  mergeSorted_postcond
    a1 a2
    (mergeSorted a1 a2 h_precond)
    h_precond.
Admitted.
