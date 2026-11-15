(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a6:
  the least constant bounding the absolute-value integral of every real cubic
  polynomial with a root in [0,1] by its maximum absolute value there is 5/6.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory integrationTheory polyTheory;

val putnam_2016_a6 =
  ``let unit_interval = interval [0, 1]
    in
    let satisfies_bound =
      \C : real.
        !P : real list.
          degree P = 3 /\
          (?x : real.
             x IN unit_interval /\
             poly P x = 0)
          ==>
          integration$integral unit_interval
            (\x : real. abs (poly P x)) <=
          C * sup
                (IMAGE
                   (\x : real. abs (poly P x))
                   unit_interval)
    in
    let solution = (5 / 6 : real)
    in
      satisfies_bound solution /\
      !C : real.
        satisfies_bound C
        ==>
        solution <= C``;
