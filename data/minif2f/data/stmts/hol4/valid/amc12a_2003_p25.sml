(*
  Statement-only formalization of miniF2F valid problem amc12a_2003_p25: classifying the
  coefficient of a real square-root function whose natural radicand domain
  equals its image. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val amc12a_2003_p25 =
  ``!a b : real. !f : real -> real.
      0 < b /\
      (!x. f x = sqrt (a * x pow 2 + b * x)) /\
      {x | 0 <= a * x pow 2 + b * x} =
        IMAGE f {x | 0 <= a * x pow 2 + b * x}
      ==>
      a = 0 \/ a = -4``;
