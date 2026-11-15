(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a3:
  strict growth and divergence to positive infinity of power-ratio integrals
  for distinct positive continuous functions with equal integrals. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;
open extrealTheory sigma_algebraTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_2017_a3 =
  ``!a b : real. !f g : real -> real. !I : num -> real.
      let interval_measure =
        restrict_space lebesgue (interval (a, b))
      in
      let integral_value =
        \h : real -> real.
          real
            (lebesgue$integral interval_measure
               (\x : real. Normal (h x)))
      in
        a < b /\
        f continuous_on interval [a, b] /\
        g continuous_on interval [a, b] /\
        (!x : real.
           x IN interval [a, b]
           ==>
           0 < f x /\ 0 < g x) /\
        integral_value f = integral_value g /\
        (?x : real.
           x IN interval [a, b] /\ f x <> g x) /\
        (!n : num.
           0 < n
           ==>
           I n =
             integral_value
               (\x : real.
                  f x pow (n + 1) / g x pow n))
        ==>
        (!n : num.
           0 < n ==> I n < I (n + 1)) /\
        (!B : real.
           ?N : num.
             !n : num.
               N <= n ==> B <= I n)``;
