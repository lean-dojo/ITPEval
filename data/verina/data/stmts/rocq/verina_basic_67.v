(* Statement-only formalization of VERINA corpus artifact verina_basic_67,
   catalog title "IsPalindrome": an executable inward scan deciding whether
   an arbitrary Unicode-character list is a palindrome, together with its
   trivial precondition, index-symmetry postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List NArith Strings.Ascii.

Definition unicode_scalar (code : N) : Prop :=
  (code < 55296)%N \/
  ((57343 < code)%N /\ (code < 1114112)%N).

Inductive lean_char : Type :=
| LeanAscii : ascii -> lean_char
| LeanNonAscii :
    forall code : N,
      (256 <= code)%N ->
      unicode_scalar code ->
      lean_char.

Definition lean_char_scalar_value (c : lean_char) : N :=
  match c with
  | LeanAscii a => N.of_nat (Ascii.nat_of_ascii a)
  | LeanNonAscii code _ _ => code
  end.

Definition lean_char_eqb (x y : lean_char) : bool :=
  N.eqb (lean_char_scalar_value x) (lean_char_scalar_value y).

Definition IsPalindrome_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition IsPalindrome_precond (_x : list lean_char) : Prop :=
  True.

Fixpoint isPalindromeHelper_fuel
    (fuel : nat)
    (x : list lean_char)
    (i j : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Nat.ltb i j then
        match nth_error x i, nth_error x j with
        | Some ci, Some cj =>
            if negb (lean_char_eqb ci cj)
            then false
            else
              isPalindromeHelper_fuel
                fuel' x (S i) (j - 1)
        | _, _ => false
        end
      else true
  end.

Definition isPalindromeHelper
    (x : list lean_char)
    (i j : nat) : bool :=
  isPalindromeHelper_fuel (S j) x i j.

Definition IsPalindrome
    (x : list lean_char)
    (_h_precond : IsPalindrome_precond x) : bool :=
  if Nat.eqb (length x) O
  then true
  else isPalindromeHelper x O (length x - 1).

Definition IsPalindrome_postcond
    (x : list lean_char)
    (result : bool)
    (_h_precond : IsPalindrome_precond x) : Prop :=
  result = true <->
  forall i : nat,
    (i < length x)%nat ->
    lean_char_scalar_value
      (nth i x IsPalindrome_default_char) =
    lean_char_scalar_value
      (nth (length x - i - 1) x IsPalindrome_default_char).

Theorem IsPalindrome_spec_satisfied
    (x : list lean_char)
    (h_precond : IsPalindrome_precond x) :
  IsPalindrome_postcond
    x (IsPalindrome x h_precond) h_precond.
Admitted.
