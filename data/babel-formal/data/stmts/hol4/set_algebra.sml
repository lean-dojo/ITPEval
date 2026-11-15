(*
  Statement-only formalization of the Babel-formal artifact set_algebra: pointwise
  distributivity and De Morgan laws for sets represented as predicates. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val sUnion_def = new_definition (
  "sUnion_def",
  ``sUnion (A : 'a -> bool) (B : 'a -> bool) =
      \x. A x \/ B x``);

val sInter_def = new_definition (
  "sInter_def",
  ``sInter (A : 'a -> bool) (B : 'a -> bool) =
      \x. A x /\ B x``);

val sCompl_def = new_definition (
  "sCompl_def",
  ``sCompl (A : 'a -> bool) =
      \x. ~A x``);

val inter_distrib_left =
  ``!(A : 'a -> bool) B C x.
      (sInter A (sUnion B C)) x <=>
      (sUnion (sInter A B) (sInter A C)) x``;

val inter_distrib_right =
  ``!(A : 'a -> bool) B C x.
      (sInter (sUnion A B) C) x <=>
      (sUnion (sInter A C) (sInter B C)) x``;

val de_morgan_union =
  ``!(A : 'a -> bool) B x.
      (sCompl (sUnion A B)) x <=>
      (sInter (sCompl A) (sCompl B)) x``;

val de_morgan_inter =
  ``!(A : 'a -> bool) B x.
      (sCompl (sInter A B)) x <=>
      (sUnion (sCompl A) (sCompl B)) x``;
