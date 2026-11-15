(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_a2:
  the real parameters admitting a continuous real function whose self-composition
  is the parameter times the ninth power. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory;

val putnam_1979_a2 =
  ``!k : real.
      ((?f : real -> real.
          f continuous_on UNIV /\
          !x : real. f (f x) = k * x pow 9)
       <=> 0 <= k)``;
