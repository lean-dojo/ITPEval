(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q189136, "Mean value theorem": Lagrange's and Cauchy's mean value theorems
  for real functions on a closed interval. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;
open topologyTheory real_topologyTheory derivativeTheory;

val exists_deriv_eq_slope =
  ``!f a b.
      a < b /\
      f continuous_on interval [a,b] /\
      f differentiable_on interval (a,b)
      ==>
      ?c.
        a < c /\ c < b /\
        vector_derivative f (at c) =
          (f b - f a) / (b - a)``;

val exists_ratio_deriv_eq_ratio_slope =
  ``!f g a b.
      a < b /\
      f continuous_on interval [a,b] /\
      g continuous_on interval [a,b] /\
      f differentiable_on interval (a,b) /\
      g differentiable_on interval (a,b)
      ==>
      ?c.
        a < c /\ c < b /\
        (g b - g a) * vector_derivative f (at c) =
          (f b - f a) * vector_derivative g (at c)``;
