(* Statement-only formalization of VERINA corpus artifact verina_basic_14,
   catalog title "containsZ": executable Boolean detection of lowercase or
   uppercase Z in an arbitrary Unicode string, together with its
   no-precondition correctness contract. This file contains no proof. *)

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

Definition containsZ_lower_z : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 122).

Definition containsZ_upper_z : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 90).

Definition containsZ_is_target (c : lean_char) : bool :=
  match c with
  | LeanAscii a =>
      orb
        (Nat.eqb (Ascii.nat_of_ascii a) 122)
        (Nat.eqb (Ascii.nat_of_ascii a) 90)
  | LeanNonAscii _ _ _ => false
  end.

Definition containsZ_precond (_s : lean_string) : Prop :=
  True.

Definition containsZ
    (s : lean_string)
    (_h_precond : containsZ_precond s) : bool :=
  existsb containsZ_is_target s.

Definition containsZ_postcond
    (s : lean_string)
    (result : bool)
    (_h_precond : containsZ_precond s) : Prop :=
  (exists x : lean_char,
      In x s /\
      (x = containsZ_lower_z \/ x = containsZ_upper_z)) <->
  result = true.

Theorem containsZ_spec_satisfied
    (s : lean_string)
    (h_precond : containsZ_precond s) :
  containsZ_postcond s (containsZ s h_precond) h_precond.
Admitted.
