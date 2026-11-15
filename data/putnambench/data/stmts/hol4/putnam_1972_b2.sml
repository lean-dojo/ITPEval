(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b2:
  the maximum elapsed time for a twice-differentiable real function whose
  second derivative is nonincreasing and whose displacement and endpoint
  velocities are prescribed. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1972_b2 =
  ``!s v : real.
      let solution = 2 * s / v
      in
      let valid =
        \t : real.
        \x : real -> real.
          (!w : real.
             0 <= w /\ w <= t
             ==>
             higher_differentiable 2 x w) /\
          (!a b : real.
             0 <= a /\ a <= b /\ b <= t
             ==>
             diffn 2 x b <= diffn 2 x a) /\
          diffn 1 x 0 = 0 /\
          diffn 1 x t = v /\
          x t - x 0 = s
      in
        0 < s /\ 0 < v
        ==>
        (?x : real -> real. valid solution x) /\
        (!t : real.
           solution < t
           ==>
           ~(?x : real -> real. valid t x))``;
