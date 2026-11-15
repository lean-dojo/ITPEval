(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q791663 (thousand-theorems__hol4__Q791663), "Beatty's theorem":
  Holder-conjugate real parameters give complementary integer Beatty
  sequences, and with an irrational parameter their positive Beatty
  sequences partition the positive integers by symmetric difference.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory realTheory intrealTheory;

val q791663_beattySeq_def = new_definition (
  "q791663_beattySeq_def",
  ``q791663_beattySeq (r : real) (k : int) =
      INT_FLOOR (real_of_int k * r)``);

val q791663_beattySeq_prime_def = new_definition (
  "q791663_beattySeq_prime_def",
  ``q791663_beattySeq_prime (r : real) (k : int) =
      INT_CEILING (real_of_int k * r) - 1``);

val q791663_holder_conjugate_def = new_definition (
  "q791663_holder_conjugate_def",
  ``q791663_holder_conjugate (r : real) (s : real) <=>
      inv r + inv s = 1 /\ 0 < r /\ 0 < s``);

val q791663_irrational_def = new_definition (
  "q791663_irrational_def",
  ``q791663_irrational (r : real) <=>
      !a b : int.
        b <> 0 ==>
        r <> real_of_int a / real_of_int b``);

val compl_beattySeq =
  ``!r s : real.
      q791663_holder_conjugate r s
      ==>
      UNIV DIFF (IMAGE (q791663_beattySeq r) UNIV) =
        IMAGE (q791663_beattySeq_prime s) UNIV``;

val Irrational_beattySeq_symmDiff_beattySeq_pos =
  ``!r s : real.
      q791663_holder_conjugate r s /\
      q791663_irrational r
      ==>
      let Br =
        IMAGE (q791663_beattySeq r) {k : int | 0 < k}
      in
      let Bs =
        IMAGE (q791663_beattySeq s) {k : int | 0 < k}
      in
        (Br DIFF Bs) UNION (Bs DIFF Br) = {n : int | 0 < n}``;
