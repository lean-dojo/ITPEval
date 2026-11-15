(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a4:
  the expected value of the dyadic sum of independent uniform unit-interval
  random variables, stopped at their first strict increase. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory
     transcTheory;
open extrealTheory measureTheory borelTheory lebesgue_measureTheory
     probabilityTheory;

val putnam_2022_a4 =
  ``let stop =
      \X : num -> 'a -> real.
      \w : 'a.
        if ?n : num. X n w < X (SUC n) w then
          count (SUC (LEAST n. X n w < X (SUC n) w))
        else
          UNIV
    in
    let stopped_sum =
      \X : num -> 'a -> real.
      \w : 'a.
        infsum (stop X w)
          (\i : num. X i w / (2 : real) pow (i + 1))
    in
      !(p : 'a p_space) (X : num -> 'a -> real).
        prob_space p /\
        p_space p = UNIV /\
        (!i : num. random_variable (X i) p Borel) /\
        (!i : num. !s : real set.
           s IN subsets Borel
           ==>
           distribution p (X i) s =
             measure lborel (s INTER interval [0, 1])) /\
        indep_vars p X (\i : num. Borel) UNIV
        ==>
        expectation p (\w : 'a. Normal (stopped_sum X w)) =
          Normal (2 * exp (1 / 2) - 3)``;
