(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q660799, "Darboux's theorem (analysis)": derivatives of real functions on
  intervals take every intermediate value, with order-connected and convex
  image formulations. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;
open topologyTheory real_topologyTheory derivativeTheory;

val exists_hasDerivWithinAt_eq_of_gt_of_lt =
  ``!(f : real -> real) (fp : real -> real)
      (a : real) (b : real) (m : real).
      a <= b /\
      (!x.
        x IN interval [a,b] ==>
        (f has_vector_derivative fp x)
          (at x within interval [a,b])) /\
      fp a < m /\
      m < fp b
      ==>
      ?c.
        c IN interval (a,b) /\
        fp c = m``;

val exists_hasDerivWithinAt_eq_of_lt_of_gt =
  ``!(f : real -> real) (fp : real -> real)
      (a : real) (b : real) (m : real).
      a <= b /\
      (!x.
        x IN interval [a,b] ==>
        (f has_vector_derivative fp x)
          (at x within interval [a,b])) /\
      m < fp a /\
      fp b < m
      ==>
      ?c.
        c IN interval (a,b) /\
        fp c = m``;

val OrdConnected_image_hasDerivWithinAt =
  ``!(f : real -> real) (fp : real -> real) (s : real set).
      is_interval s /\
      (!x.
        x IN s ==>
        (f has_vector_derivative fp x) (at x within s))
      ==>
      is_interval (IMAGE fp s)``;

val OrdConnected_image_derivWithin =
  ``!(f : real -> real) (s : real set).
      is_interval s /\
      f differentiable_on s
      ==>
      is_interval
        (IMAGE (\x. vector_derivative f (at x within s)) s)``;

val OrdConnected_image_deriv =
  ``!(f : real -> real) (s : real set).
      is_interval s /\
      (!x. x IN s ==> f differentiable (at x))
      ==>
      is_interval (IMAGE (\x. vector_derivative f (at x)) s)``;

val Convex_image_hasDerivWithinAt =
  ``!(f : real -> real) (fp : real -> real) (s : real set).
      convex s /\
      (!x.
        x IN s ==>
        (f has_vector_derivative fp x) (at x within s))
      ==>
      convex (IMAGE fp s)``;

val Convex_image_derivWithin =
  ``!(f : real -> real) (s : real set).
      convex s /\
      f differentiable_on s
      ==>
      convex
        (IMAGE (\x. vector_derivative f (at x within s)) s)``;

val Convex_image_deriv =
  ``!(f : real -> real) (s : real set).
      convex s /\
      (!x. x IN s ==> f differentiable (at x))
      ==>
      convex (IMAGE (\x. vector_derivative f (at x)) s)``;

val exists_hasDerivWithinAt_eq_of_ge_of_le =
  ``!(f : real -> real) (fp : real -> real)
      (a : real) (b : real) (m : real).
      a <= b /\
      (!x.
        x IN interval [a,b] ==>
        (f has_vector_derivative fp x)
          (at x within interval [a,b])) /\
      fp a <= m /\
      m <= fp b
      ==>
      ?c.
        c IN interval [a,b] /\
        fp c = m``;

val exists_hasDerivWithinAt_eq_of_le_of_ge =
  ``!(f : real -> real) (fp : real -> real)
      (a : real) (b : real) (m : real).
      a <= b /\
      (!x.
        x IN interval [a,b] ==>
        (f has_vector_derivative fp x)
          (at x within interval [a,b])) /\
      m <= fp a /\
      fp b <= m
      ==>
      ?c.
        c IN interval [a,b] /\
        fp c = m``;
