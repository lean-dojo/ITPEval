(*
  Statement-only formalization of the Babel-formal artifact zero_le_one_elem:
  zero and one matrices, pointwise matrix order, and pointwise matrix equality.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val one_matrix_def = new_definition (
  "one_matrix_def",
  ``one_matrix (decEq : 'm -> 'm -> bool) (oneA : 'a) (zeroA : 'a)
      (i : 'm) (j : 'm) =
      if decEq i j then oneA else zeroA``);

val zero_matrix_def = new_definition (
  "zero_matrix_def",
  ``zero_matrix (zeroA : 'a) (i : 'm) (j : 'm) = zeroA``);

val matrix_le_def = new_definition (
  "matrix_le_def",
  ``matrix_le (le_rel : 'a -> 'a -> bool)
      (A0 : 'm -> 'm -> 'a) (B0 : 'm -> 'm -> 'a) <=>
      !i j. le_rel (A0 i j) (B0 i j)``);

val matrix_eq_def = new_definition (
  "matrix_eq_def",
  ``matrix_eq (A0 : 'm -> 'm -> 'a) (B0 : 'm -> 'm -> 'a) <=>
      !i j. A0 i j = B0 i j``);

val zero_le_one_elem =
  ``!(decEq : 'm -> 'm -> bool) (zeroA : 'a) (oneA : 'a)
      (le_rel : 'a -> 'a -> bool) (i : 'm) (j : 'm).
      le_rel zeroA oneA ==>
      le_rel zeroA zeroA ==>
      le_rel zeroA (one_matrix decEq oneA zeroA i j)``;

val zero_le_one_matrix =
  ``!(decEq : 'm -> 'm -> bool) (zeroA : 'a) (oneA : 'a)
      (le_rel : 'a -> 'a -> bool).
      le_rel zeroA oneA ==>
      le_rel zeroA zeroA ==>
      matrix_le le_rel (zero_matrix zeroA)
        (one_matrix decEq oneA zeroA)``;

val matrix_le_refl =
  ``!(le_rel : 'a -> 'a -> bool).
      (!x. le_rel x x) ==>
      !A0 : 'm -> 'm -> 'a. matrix_le le_rel A0 A0``;

val matrix_le_trans =
  ``!(le_rel : 'a -> 'a -> bool).
      (!x y z. le_rel x y ==> le_rel y z ==> le_rel x z) ==>
      !A0 B0 C0 : 'm -> 'm -> 'a.
        matrix_le le_rel A0 B0 ==>
        matrix_le le_rel B0 C0 ==>
        matrix_le le_rel A0 C0``;

val matrix_eq_refl =
  ``!A0 : 'm -> 'm -> 'a. matrix_eq A0 A0``;

val matrix_eq_sym =
  ``!A0 B0 : 'm -> 'm -> 'a.
      matrix_eq A0 B0 ==> matrix_eq B0 A0``;

val matrix_eq_trans =
  ``!A0 B0 C0 : 'm -> 'm -> 'a.
      matrix_eq A0 B0 ==>
      matrix_eq B0 C0 ==>
      matrix_eq A0 C0``;

val matrix_eq_le =
  ``!(le_rel : 'a -> 'a -> bool).
      (!x. le_rel x x) ==>
      !A0 B0 : 'm -> 'm -> 'a.
        matrix_eq A0 B0 ==>
        matrix_le le_rel A0 B0 /\ matrix_le le_rel B0 A0``;

val matrix_le_antisymm =
  ``!(le_rel : 'a -> 'a -> bool).
      (!x y. le_rel x y ==> le_rel y x ==> x = y) ==>
      !A0 B0 : 'm -> 'm -> 'a.
        matrix_le le_rel A0 B0 ==>
        matrix_le le_rel B0 A0 ==>
        matrix_eq A0 B0``;
