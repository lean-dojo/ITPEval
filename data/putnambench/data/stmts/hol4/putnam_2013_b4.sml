(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b4:
  the variance of a product of continuous real functions on the unit interval
  is bounded using their variances and maximum absolute values. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory integrationTheory;

val putnam_2013_b4 =
  ``!f g : real -> real.
      f continuous_on interval [0, 1] /\
      g continuous_on interval [0, 1]
      ==>
      let mu =
        \h : real -> real.
          integration$integral (interval [0, 1]) h
      in
      let variance =
        \h : real -> real.
          integration$integral (interval [0, 1])
            (\x : real. (h x - mu h) pow 2)
      in
      let maximum =
        \h : real -> real.
          sup (IMAGE (\x : real. abs (h x)) (interval [0, 1]))
      in
        variance (\x : real. f x * g x) <=
          2 * variance f * maximum g pow 2 +
          2 * variance g * maximum f pow 2``;
