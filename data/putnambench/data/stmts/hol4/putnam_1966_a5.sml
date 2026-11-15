(*
  Statement-only formalization of PutnamBench artifact putnam_1966_a5:
  every linear local operator on the continuous real-valued functions is
  pointwise multiplication by a continuous function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory;

val putnam_1966_a5 =
  ``!C : (real -> real) set.
    !T : (real -> real) -> (real -> real).
      C = {f : real -> real | f continuous_on UNIV} /\
      (!f : real -> real.
         f IN C
         ==>
         T f IN C) /\
      (!a b : real. !f g : real -> real.
         f IN C /\ g IN C
         ==>
         T (\x : real. a * f x + b * g x) =
           (\x : real. a * T f x + b * T g x)) /\
      (!r s : real.
         r <= s
         ==>
         !f g : real -> real.
           f IN C /\ g IN C /\
           (!x : real.
              r <= x /\ x <= s
              ==>
              f x = g x)
           ==>
           !x : real.
             r <= x /\ x <= s
             ==>
             T f x = T g x)
      ==>
      ?h : real -> real.
        h IN C /\
        !g : real -> real.
          g IN C
          ==>
          T g = (\x : real. h x * g x)``;
