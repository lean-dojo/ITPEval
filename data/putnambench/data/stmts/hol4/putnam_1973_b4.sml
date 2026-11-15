(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b4:
  the integral inequality for globally continuously differentiable real
  functions with derivative in (0,1], together with an equality example.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory integrationTheory;

val putnam_1973_b4 =
  ``let hprop =
      \g : real -> real.
        (!x : real. higher_differentiable 1 g x) /\
        (\x : real. diffn 1 g x) continuous_on UNIV /\
        (!x : real. 0 < diffn 1 g x /\ diffn 1 g x <= 1) /\
        g 0 = 0
    in
      let solution = \x : real. x
      in
        !f : real -> real.
          hprop f
          ==>
          integration$integral (interval [0, 1])
            (\x : real. f x pow 3) <=
            (integration$integral (interval [0, 1]) f) pow 2 /\
          hprop solution /\
          (integration$integral (interval [0, 1]) solution) pow 2 =
            integration$integral (interval [0, 1])
              (\x : real. solution x pow 3)``;
