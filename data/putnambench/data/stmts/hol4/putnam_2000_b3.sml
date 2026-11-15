(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b3:
  monotonicity and convergence to twice the degree of the zero counts, with
  multiplicity, of successive derivatives of a real trigonometric polynomial.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory limTheory
     transcTheory;

val putnam_2000_b3 =
  ``let nat_tsum_on =
      \(s : real -> bool) (h : real -> num).
        if FINITE {x : real | x IN s /\ h x <> 0}
        then SIGMA h {x : real | x IN s /\ h x <> 0}
        else 0
    in
      !N : num.
      !a : num -> real.
      !f : real -> real.
      !mult : (real -> real) -> real -> num.
      !M : num -> num.
        0 < N /\
        a N <> 0 /\
        (!t : real.
           f t =
             SIGMA
               (\j : num. a j * sin (2 * pi * &j * t))
               (IMAGE SUC (count N))) /\
        (!g : real -> real.
         !t : real.
           (?c : num. diffn c g t <> 0)
           ==>
           diffn (mult g t) g t <> 0 /\
           !k : num. k < mult g t ==> diffn k g t = 0) /\
        (!k : num.
           M k =
             nat_tsum_on
               {t : real | 0 <= t /\ t < 1}
               (\t : real. mult (diffn k f) t))
        ==>
        (!i j : num. i <= j ==> M i <= M j) /\
        ?K : num. !k : num. K <= k ==> M k = 2 * N``;
