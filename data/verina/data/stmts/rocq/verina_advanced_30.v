(* Statement-only formalization of VERINA corpus artifact verina_advanced_30,
   catalog title "longestIncreasingStreak": an executable scan computing the
   longest strictly increasing contiguous streak in an integer list, together
   with its exact-streak and maximality contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition longestIncreasingStreak_precond
    (_nums : list Z) : Prop :=
  True.

Fixpoint longestIncreasingStreak_aux
    (lst : list Z)
    (prev : option Z)
    (currLen maxLen : nat) : nat :=
  match lst with
  | [] => Nat.max currLen maxLen
  | x :: xs =>
      match prev with
      | None =>
          longestIncreasingStreak_aux
            xs (Some x) 1%nat (Nat.max 1%nat maxLen)
      | Some p =>
          if Z.gtb x p
          then
            longestIncreasingStreak_aux
              xs (Some x) (currLen + 1) (Nat.max (currLen + 1) maxLen)
          else
            longestIncreasingStreak_aux
              xs (Some x) 1%nat (Nat.max currLen maxLen)
      end
  end.

Definition longestIncreasingStreak
    (nums : list Z)
    (_h_precond : longestIncreasingStreak_precond nums) : nat :=
  longestIncreasingStreak_aux nums None 0%nat 0%nat.

Definition longestIncreasingStreak_get
    (nums : list Z) (index : nat) : Z :=
  nth index nums 0%Z.

Definition longestIncreasingStreak_exact_streak
    (nums : list Z)
    (result start : nat) : bool :=
  andb
    (Nat.leb (start + result) (length nums))
    (andb
      (forallb
        (fun i =>
          Z.ltb
            (longestIncreasingStreak_get nums (start + i))
            (longestIncreasingStreak_get nums (start + i + 1)))
        (seq 0%nat (result - 1)))
      (andb
        (orb
          (Nat.eqb start 0%nat)
          (Z.geb
            (longestIncreasingStreak_get nums (start - 1))
            (longestIncreasingStreak_get nums start)))
        (orb
          (Nat.eqb (start + result) (length nums))
          (Z.geb
            (longestIncreasingStreak_get
              nums (start + result - 1))
            (longestIncreasingStreak_get
              nums (start + result)))))).

Definition longestIncreasingStreak_has_break
    (nums : list Z)
    (result start : nat) : bool :=
  existsb
    (fun i =>
      orb
        (Nat.leb (length nums) (start + i + 1))
        (Z.geb
          (longestIncreasingStreak_get nums (start + i))
          (longestIncreasingStreak_get nums (start + i + 1))))
    (seq 0%nat result).

Definition longestIncreasingStreak_postcond
    (nums : list Z)
    (result : nat)
    (_h_precond : longestIncreasingStreak_precond nums) : Prop :=
  (nums = [] -> result = 0%nat) /\
  ((0 < result)%nat ->
    existsb
      (longestIncreasingStreak_exact_streak nums result)
      (seq 0%nat (length nums - result + 1)) = true) /\
  forallb
    (longestIncreasingStreak_has_break nums result)
    (seq 0%nat (length nums - result)) = true.

Theorem longestIncreasingStreak_spec_satisfied
    (nums : list Z)
    (h_precond : longestIncreasingStreak_precond nums) :
  longestIncreasingStreak_postcond
    nums
    (longestIncreasingStreak nums h_precond)
    h_precond.
Admitted.
