(*
  Statement-only formalization of Thousand Theorems corpus artifact
  thousand-theorems__hol4__Q5171652, "Corners theorem": every sufficiently
  dense finite subset of {0, ..., n - 1} squared contains a nontrivial
  additive corner once n meets the explicit regularity-lemma cutoff. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinTheory pairTheory pred_setTheory;
open realTheory transcTheory;

val q5171652_step_bound_def = new_definition (
  "q5171652_step_bound_def",
  ``q5171652_step_bound (n : num) = n * 4 EXP n``);

val q5171652_initial_bound_def = new_definition (
  "q5171652_initial_bound_def",
  ``q5171652_initial_bound (epsilon : real) (l : num) =
      MAX 7
        (MAX l
          (NUM_FLOOR
            (ln (100 / epsilon pow 5) / ln 4) + 1))``);

val q5171652_regularity_bound_def = new_definition (
  "q5171652_regularity_bound_def",
  ``q5171652_regularity_bound (epsilon : real) (l : num) =
      let b =
        FUNPOW q5171652_step_bound
          (NUM_FLOOR (4 / epsilon pow 5))
          (q5171652_initial_bound epsilon l)
      in
        b * 16 EXP b``);

val q5171652_triangle_removal_bound_def = new_definition (
  "q5171652_triangle_removal_bound_def",
  ``q5171652_triangle_removal_bound (epsilon : real) =
      min
        (inv (&(2 * NUM_CEILING (4 / epsilon) EXP 3)))
        ((1 - min 1 epsilon / 4) *
          (epsilon /
            (16 *
              &(q5171652_regularity_bound
                (epsilon / 8)
                (NUM_CEILING (4 / epsilon))))) pow 3)``);

val q5171652_corners_theorem_bound_def = new_definition (
  "q5171652_corners_theorem_bound_def",
  ``q5171652_corners_theorem_bound (epsilon : real) =
      NUM_FLOOR
        (inv
          (q5171652_triangle_removal_bound (epsilon / 9) * 27)) + 1``);

val q5171652_corner_free_def = new_definition (
  "q5171652_corner_free_def",
  ``q5171652_corner_free (A : (num # num) set) <=>
      !x1 y1 x2 y2 : num.
        (x1,y1) IN A /\
        (x1,y2) IN A /\
        (x2,y1) IN A /\
        x1 + y2 = x2 + y1
        ==>
        x1 = x2``);

val corners_theorem_nat =
  ``!epsilon : real. !n : num. !A : (num # num) set.
      0 < epsilon /\
      q5171652_corners_theorem_bound (epsilon / 9) <= n /\
      FINITE A /\
      (!p. p IN A ==> FST p < n /\ SND p < n) /\
      epsilon * (&n pow 2) <= &(CARD A)
      ==>
      ~q5171652_corner_free A``;
