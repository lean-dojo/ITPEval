(*
  Statement-only formalization of "Solutions to Pell's Equation" from
  the Hundred Theorems corpus. For each nonsquare natural parameter,
  a positive fundamental solution generates every integer solution by
  the Pell recurrence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val solutions_to_pells_equation =
  ``!D : num.
      ~(?k : num. D = k EXP 2) ==>
      ?x0 y0 : num.
      ?p : num -> num # num.
        0 < y0 /\
        x0 EXP 2 = 1 + D * y0 EXP 2 /\
        p 0 = (1, 0) /\
        (!n : num.
          p (SUC n) =
            (FST (p n) * x0 + D * SND (p n) * y0,
             FST (p n) * y0 + SND (p n) * x0)) /\
        (!(x : int) (y : int).
          x * x - &D * (y * y) = 1 <=>
          ?n : num.
            (x = &(FST (p n)) \/ x = -(&(FST (p n)))) /\
            (y = &(SND (p n)) \/ y = -(&(SND (p n)))))``;
