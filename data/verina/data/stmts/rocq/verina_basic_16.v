(* Statement-only formalization of VERINA corpus artifact verina_basic_16,
   catalog title "replaceChars": executable replacement of every occurrence
   of one character by another in an arbitrary Unicode string, together with
   length preservation and pointwise correctness. This file contains no
   proof. *)

From Stdlib Require Import
  Arith.PeanoNat
  Bool.Bool
  Lists.List
  Logic.ProofIrrelevance
  NArith
  Strings.Ascii.

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

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Definition replaceChars_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition replaceChars_precond
    (_s : lean_string)
    (_oldChar _newChar : lean_char) : Prop :=
  True.

Definition replaceChars
    (s : lean_string)
    (oldChar newChar : lean_char)
    (_h_precond : replaceChars_precond s oldChar newChar) : lean_string :=
  map
    (fun c =>
      if lean_char_eqb c oldChar
      then newChar
      else c)
    s.

Definition replaceChars_postcond
    (s : lean_string)
    (oldChar newChar : lean_char)
    (result : lean_string)
    (_h_precond : replaceChars_precond s oldChar newChar) : Prop :=
  length result = length s /\
  forall i : nat,
    i < length s ->
    (nth i s replaceChars_default_char = oldChar ->
      nth i result replaceChars_default_char = newChar) /\
    (nth i s replaceChars_default_char <> oldChar ->
      nth i result replaceChars_default_char =
        nth i s replaceChars_default_char).

Theorem replaceChars_spec_satisfied
    (s : lean_string)
    (oldChar newChar : lean_char)
    (h_precond : replaceChars_precond s oldChar newChar) :
  replaceChars_postcond
    s oldChar newChar
    (replaceChars s oldChar newChar h_precond)
    h_precond.
Admitted.
