(* Statement-only formalization of VERINA corpus artifact verina_basic_36,
   catalog title "replaceWithColon": executable replacement of every space,
   comma, or dot in an arbitrary Unicode string by a colon, together with
   length preservation, pointwise correctness, and the final correctness
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

Definition lean_string := list lean_char.

Definition lean_char_eqb (x y : lean_char) : bool :=
  match x, y with
  | LeanAscii a, LeanAscii b =>
      Nat.eqb (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
  | LeanNonAscii xcode _ _, LeanNonAscii ycode _ _ =>
      N.eqb xcode ycode
  | _, _ => false
  end.

Definition replaceWithColon_space : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 32).

Definition replaceWithColon_comma : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 44).

Definition replaceWithColon_dot : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 46).

Definition replaceWithColon_colon : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 58).

Definition replaceWithColon_default_char : lean_char :=
  LeanAscii (Ascii.ascii_of_nat 0).

Definition isSpaceCommaDot (c : lean_char) : bool :=
  if lean_char_eqb c replaceWithColon_space then true
  else if lean_char_eqb c replaceWithColon_comma then true
  else if lean_char_eqb c replaceWithColon_dot then true
  else false.

Definition replaceWithColon_precond (_s : lean_string) : Prop :=
  True.

Definition replaceWithColon
    (s : lean_string)
    (_h_precond : replaceWithColon_precond s) : lean_string :=
  map
    (fun c =>
      if isSpaceCommaDot c
      then replaceWithColon_colon
      else c)
    s.

Definition replaceWithColon_postcond
    (s result : lean_string)
    (_h_precond : replaceWithColon_precond s) : Prop :=
  length result = length s /\
  forall i : nat,
    i < length s ->
    (isSpaceCommaDot
       (nth i s replaceWithColon_default_char) = true ->
      nth i result replaceWithColon_default_char =
        replaceWithColon_colon) /\
    (isSpaceCommaDot
       (nth i s replaceWithColon_default_char) <> true ->
      nth i result replaceWithColon_default_char =
        nth i s replaceWithColon_default_char).

Theorem replaceWithColon_spec_satisfied
    (s : lean_string)
    (h_precond : replaceWithColon_precond s) :
  replaceWithColon_postcond
    s (replaceWithColon s h_precond) h_precond.
Admitted.
