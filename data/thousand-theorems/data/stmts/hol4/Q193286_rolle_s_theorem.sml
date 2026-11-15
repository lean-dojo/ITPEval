(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q193286, "Rolle's theorem": a real function continuous on a closed interval
  with equal endpoint values has an interior point where its totalized
  derivative, defined to be zero at nondifferentiable points, is zero. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;
open topologyTheory real_topologyTheory derivativeTheory;

val exists_deriv_eq_zero =
  ``let deriv0 =
      \f : real -> real.
        \x : real.
          if f differentiable (at x) then vector_derivative f (at x) else 0
    in
      !(f : real -> real) (a : real) (b : real).
        a < b /\
        f continuous_on interval [a,b] /\
        f a = f b
        ==>
        ?c : real.
          a < c /\ c < b /\
          deriv0 f c = 0``;
