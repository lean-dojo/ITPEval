(*
  Statement-only formalization of Thousand Theorems corpus artifact Q22952648
  (thousand-theorems__rocq__Q22952648), "Uncountability of the continuum":
  the universal set of real numbers is not countable. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Definition q22952648_countable (A : Type) : Prop :=
  exists encode : A -> nat,
    forall x y : A, encode x = encode y -> x = y.

Theorem uncountability_of_the_continuum :
  ~ q22952648_countable R.
Admitted.
