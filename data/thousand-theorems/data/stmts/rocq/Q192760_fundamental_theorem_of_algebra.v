(*
  Statement-only formalization of Thousand Theorems corpus artifact Q192760
  (thousand-theorems__rocq__Q192760), "Fundamental theorem of algebra":
  the complex numbers are algebraically closed, expressed by the fact that
  every nonconstant complex polynomial has a complex root.
  This file contains no proof.
*)

From Stdlib Require Import List Reals.

Import ListNotations.
Local Open Scope R_scope.

Definition q192760_C : Type := (R * R)%type.

Definition q192760_zero : q192760_C := (0, 0).

Definition q192760_add (z w : q192760_C) : q192760_C :=
  (fst z + fst w, snd z + snd w).

Definition q192760_mul (z w : q192760_C) : q192760_C :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Fixpoint q192760_eval
    (coefficients : list q192760_C) (z : q192760_C) : q192760_C :=
  match coefficients with
  | [] => q192760_zero
  | coefficient :: higher_coefficients =>
      q192760_add coefficient
        (q192760_mul z (q192760_eval higher_coefficients z))
  end.

Fixpoint q192760_some_nonzero
    (coefficients : list q192760_C) : Prop :=
  match coefficients with
  | [] => False
  | coefficient :: higher_coefficients =>
      coefficient <> q192760_zero \/
      q192760_some_nonzero higher_coefficients
  end.

Definition q192760_nonconstant
    (coefficients : list q192760_C) : Prop :=
  match coefficients with
  | [] => False
  | _ :: positive_degree_coefficients =>
      q192760_some_nonzero positive_degree_coefficients
  end.

Definition q192760_is_algebraically_closed : Prop :=
  forall coefficients : list q192760_C,
    q192760_nonconstant coefficients ->
    exists z : q192760_C,
      q192760_eval coefficients z = q192760_zero.

Theorem Complex_isAlgClosed :
  q192760_is_algebraically_closed.
Admitted.
