(* Statement-only formalization of VERINA corpus artifact verina_basic_42,
   catalog title "countDigits": executable counting of ASCII digit characters
   in an arbitrary Unicode string, together with its no-precondition
   correctness contract. This file contains no proof. *)

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

Definition lean_string := list lean_char.

Definition isDigit (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      andb
        (Nat.leb 48 (Ascii.nat_of_ascii a))
        (Nat.leb (Ascii.nat_of_ascii a) 57)
  | LeanNonAscii _ _ _ => false
  end.

Definition countDigits_precond (_s : lean_string) : Prop :=
  True.

Definition countDigits
    (s : lean_string)
    (_h_precond : countDigits_precond s) : nat :=
  length (filter isDigit s).

Definition countDigits_postcond
    (s : lean_string)
    (result : nat)
    (_h_precond : countDigits_precond s) : Prop :=
  Nat.sub result (length (filter isDigit s)) = 0%nat /\
  Nat.sub (length (filter isDigit s)) result = 0%nat.

Theorem countDigits_spec_satisfied
    (s : lean_string)
    (h_precond : countDigits_precond s) :
  countDigits_postcond s (countDigits s h_precond) h_precond.
Admitted.
