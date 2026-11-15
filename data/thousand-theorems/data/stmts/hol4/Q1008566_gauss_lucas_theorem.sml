(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1008566, "Gauss–Lucas theorem": roots of the derivative of a positive-degree
  complex polynomial lie in the real convex hull of its roots, with the
  source's explicit root-multiplicity center-of-mass formula. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory complexTheory;

val gauss_lucas_poly_def = new_definition (
  "gauss_lucas_poly_def",
  ``gauss_lucas_poly (P : complex list) <=>
      P = [] \/ LAST P <> 0``);

val gauss_lucas_degree_def = new_definition (
  "gauss_lucas_degree_def",
  ``gauss_lucas_degree (P : complex list) =
      PRE (LENGTH P)``);

val gauss_lucas_eval_def = new_definition (
  "gauss_lucas_eval_def",
  ``gauss_lucas_eval (P : complex list) (z : complex) =
      FOLDR (\a acc. a + acc * z) 0 P``);

val gauss_lucas_derivative_def = new_definition (
  "gauss_lucas_derivative_def",
  ``gauss_lucas_derivative (P : complex list) =
      GENLIST
        (\k.
           complex_of_real (real_of_num (SUC k)) *
           EL (SUC k) P)
        (PRE (LENGTH P))``);

val gauss_lucas_root_set_def = new_definition (
  "gauss_lucas_root_set_def",
  ``gauss_lucas_root_set (P : complex list) =
      {z : complex | gauss_lucas_eval P z = 0}``);

val gauss_lucas_root_multiplicity_def = new_definition (
  "gauss_lucas_root_multiplicity_def",
  ``gauss_lucas_root_multiplicity
      (P : complex list) (w : complex) =
      MAX_SET
        {n : num |
           ?Q : complex list.
             !z : complex.
               gauss_lucas_eval P z =
               (z - w) pow n * gauss_lucas_eval Q z}``);

val gauss_lucas_real_sum_def = new_definition (
  "gauss_lucas_real_sum_def",
  ``gauss_lucas_real_sum (f : complex -> real) (s : complex -> bool) =
      ITSET (\z acc. f z + acc) s 0``);

val gauss_lucas_complex_sum_def = new_definition (
  "gauss_lucas_complex_sum_def",
  ``gauss_lucas_complex_sum
      (f : complex -> complex) (s : complex -> bool) =
      ITSET (\z acc. f z + acc) s 0``);

val gauss_lucas_deriv_root_weight_def = new_definition (
  "gauss_lucas_deriv_root_weight_def",
  ``gauss_lucas_deriv_root_weight
      (P : complex list) (z : complex) (w : complex) : real =
      if gauss_lucas_eval P z = 0 then
        if w = z then 1 else 0
      else
        real_of_num (gauss_lucas_root_multiplicity P w) /
        modu (z - w) pow 2``);

val gauss_lucas_center_mass_def = new_definition (
  "gauss_lucas_center_mass_def",
  ``gauss_lucas_center_mass (P : complex list) (z : complex) =
      complex_scalar_lmul
        (inv
          (gauss_lucas_real_sum
            (gauss_lucas_deriv_root_weight P z)
            (gauss_lucas_root_set P)))
        (gauss_lucas_complex_sum
          (\w.
             complex_scalar_lmul
               (gauss_lucas_deriv_root_weight P z w)
               w)
          (gauss_lucas_root_set P))``);

val gauss_lucas_in_convex_hull_def = new_definition (
  "gauss_lucas_in_convex_hull_def",
  ``gauss_lucas_in_convex_hull
      (s : complex -> bool) (z : complex) <=>
      ?t : complex -> bool. ?a : complex -> real.
        FINITE t /\
        t SUBSET s /\
        (!w. w IN t ==> 0 <= a w) /\
        gauss_lucas_real_sum a t = 1 /\
        z =
          gauss_lucas_complex_sum
            (\w. complex_scalar_lmul (a w) w)
            t``);

val Polynomial_eq_centerMass_of_eval_derivative_eq_zero =
  ``!P : complex list. !z : complex.
      gauss_lucas_poly P /\
      0 < gauss_lucas_degree P /\
      gauss_lucas_eval (gauss_lucas_derivative P) z = 0
      ==>
      z = gauss_lucas_center_mass P z``;

val Polynomial_rootSet_derivative_subset_convexHull_rootSet =
  ``!P : complex list.
      gauss_lucas_poly P /\
      0 < gauss_lucas_degree P
      ==>
      gauss_lucas_root_set (gauss_lucas_derivative P)
      SUBSET
      {z : complex |
         gauss_lucas_in_convex_hull
           (gauss_lucas_root_set P)
           z}``;
