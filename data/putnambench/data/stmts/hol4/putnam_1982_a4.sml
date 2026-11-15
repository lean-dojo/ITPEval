(*
  Statement-only formalization of PutnamBench artifact putnam_1982_a4:
  the unique global continuously differentiable real solution of
  y' = -z^3 and z' = y^3 with y(0) = 1 and z(0) = 0 has a shared positive
  period. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_1982_a4 =
  ``let hdiffeq =
      \y z : real -> real.
        y 0 = 1 /\
        z 0 = 0 /\
        (!x : real. higher_differentiable 1 y x) /\
        (\x : real. diffn 1 y x) continuous_on UNIV /\
        (!x : real. higher_differentiable 1 z x) /\
        (\x : real. diffn 1 z x) continuous_on UNIV /\
        (!x : real.
           diffn 1 y x = -(z x pow 3) /\
           diffn 1 z x = y x pow 3)
    in
      !f g : real -> real.
        hdiffeq f g /\
        ~(?f' g' : real -> real.
            (f <> f' \/ g <> g') /\
            hdiffeq f' g')
        ==>
        ?L : real.
          0 < L /\
          !x : real.
            f (x + L) = f x /\
            g (x + L) = g x``;
