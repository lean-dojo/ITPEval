(* Statement-only formalization of VERINA corpus artifact verina_basic_61,
   catalog title "allDigits": an executable left-to-right test that every
   character in an arbitrary Unicode string is an ASCII decimal digit,
   together with its no-precondition correctness contract. This file contains
   no proof. *)

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

Definition allDigits_precond (_s : lean_string) : Prop :=
  True.

Fixpoint allDigits_loop (remaining : lean_string) : bool :=
  match remaining with
  | nil => true
  | cons c rest =>
      if negb (isDigit c)
      then false
      else allDigits_loop rest
  end.

Definition allDigits
    (s : lean_string)
    (_h_precond : allDigits_precond s) : bool :=
  allDigits_loop s.

Definition allDigits_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : allDigits_precond s) : Prop :=
  result = true <->
  forall c : lean_char, In c s -> isDigit c = true.

Theorem allDigits_spec_satisfied
    (s : lean_string)
    (h_precond : allDigits_precond s) :
  allDigits_postcond s (allDigits s h_precond) h_precond.
Admitted.
