(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a3:
  the integral formula for the solution of an iterated Euler differential
  equation with vanishing initial derivatives. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;
open limTheory integrationTheory;

val putnam_1963_a3 =
  ``let solution =
      \f : real -> real.
      \n : num.
      \x : real.
      \t : real.
        (x - t) pow (n - 1) * f t / (&(FACT (n - 1)) * t pow n)
    in
      !P : num -> (real -> real) -> (real -> real).
      !n : num. !f y : real -> real.
        (!g : real -> real. P 0 g = g) /\
        (!i : num. !g : real -> real.
           P (SUC i) g =
             P i (\x : real. x * diffn 1 g x - &i * g x)) /\
        0 < n /\
        f continuous_on {x : real | 1 <= x} /\
        (!x : real.
           1 <= x
           ==>
           higher_differentiable n y x) /\
        (!k : num.
           k <= n
           ==>
           (diffn k y) continuous_on {x : real | 1 <= x})
        ==>
        ((!k : num.
            k < n
            ==>
            diffn k y 1 = 0) /\
         (!x : real.
            1 <= x
            ==>
            P n y x = f x)
         <=>
         !x : real.
           1 <= x
           ==>
           y x =
             integration$integral (interval [1, x])
               (solution f n x))``;
