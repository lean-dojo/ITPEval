(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1137206, "Taylor's theorem": the Lagrange and Cauchy forms of the
  remainder for a real function on a closed interval. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open topologyTheory real_topologyTheory derivativeTheory;

val q1137206_iterated_deriv_within_def = new_definition (
  "q1137206_iterated_deriv_within_def",
  ``q1137206_iterated_deriv_within
      n (f : real -> real) (s : real set) =
      FUNPOW
        (\g. \y. vector_derivative g (at y within s))
        n f``);

val q1137206_taylor_within_eval_def = new_definition (
  "q1137206_taylor_within_eval_def",
  ``q1137206_taylor_within_eval
      (f : real -> real) n (s : real set) x0 x =
      SIGMA
        (\k.
          q1137206_iterated_deriv_within k f s x0 /
            &(FACT k) *
          (x - x0) pow k)
        (count (SUC n))``);

val q1137206_cont_diff_on_def = new_definition (
  "q1137206_cont_diff_on_def",
  ``q1137206_cont_diff_on
      n (f : real -> real) (s : real set) <=>
      (!m.
        m <= n ==>
        q1137206_iterated_deriv_within m f s continuous_on s) /\
      (!m.
        m < n ==>
        q1137206_iterated_deriv_within m f s differentiable_on s)``);

val taylor_mean_remainder_lagrange =
  ``!f x x0 n.
      x0 < x /\
      q1137206_cont_diff_on n f (interval [x0,x]) /\
      q1137206_iterated_deriv_within n f (interval [x0,x])
        differentiable_on interval (x0,x)
      ==>
      ?x'.
        x0 < x' /\ x' < x /\
        f x -
          q1137206_taylor_within_eval f n (interval [x0,x]) x0 x =
        q1137206_iterated_deriv_within
            (SUC n) f (interval [x0,x]) x' *
          (x - x0) pow (SUC n) / &(FACT (SUC n))``;

val taylor_mean_remainder_cauchy =
  ``!f x x0 n.
      x0 < x /\
      q1137206_cont_diff_on n f (interval [x0,x]) /\
      q1137206_iterated_deriv_within n f (interval [x0,x])
        differentiable_on interval (x0,x)
      ==>
      ?x'.
        x0 < x' /\ x' < x /\
        f x -
          q1137206_taylor_within_eval f n (interval [x0,x]) x0 x =
        q1137206_iterated_deriv_within
            (SUC n) f (interval [x0,x]) x' *
          (x - x') pow n / &(FACT n) * (x - x0)``;
