(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a6:
  a lower bound on an integrable function over the unit interval from its
  vanishing lower moments and normalized nth moment. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1972_a6 =
  ``!(f : real -> real) (n : num).
      let unit_interval =
        restrict_space lebesgue (interval [0, 1])
      in
        integrable unit_interval (Normal o f) /\
        (!i. i < n ==>
             integral unit_interval
               (\x. Normal (x pow i * f x)) = 0) /\
        integral unit_interval
          (\x. Normal (x pow n * f x)) = 1
        ==>
        ?S : real set.
          S SUBSET interval [0, 1] /\
          S IN measurable_sets lebesgue /\
          0 < measure lebesgue S /\
          !x. x IN S ==>
              (&2 : real) pow n * &(n + 1) <= abs (f x)``;
