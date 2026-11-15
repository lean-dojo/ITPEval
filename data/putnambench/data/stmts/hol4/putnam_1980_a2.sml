(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a2:
  counting ordered quadruples of positive natural numbers whose four
  triple least common multiples all equal 3^r * 7^s. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory pred_setTheory;

val putnam_1980_a2 =
  ``!r : num. !s : num.
      0 < r /\ 0 < s
      ==>
      let target = 3 EXP r * 7 EXP s in
      let quadruples =
        {q : (num # num) # (num # num) |
           0 < FST (FST q) /\
           0 < SND (FST q) /\
           0 < FST (SND q) /\
           0 < SND (SND q) /\
           target =
             lcm (lcm (FST (FST q)) (SND (FST q))) (FST (SND q)) /\
           target =
             lcm (lcm (FST (FST q)) (SND (FST q))) (SND (SND q)) /\
           target =
             lcm (lcm (FST (FST q)) (FST (SND q))) (SND (SND q)) /\
           target =
             lcm (lcm (SND (FST q)) (FST (SND q))) (SND (SND q))}
      in
        FINITE quadruples /\
        CARD quadruples =
          (1 + 4 * r + 6 * r EXP 2) *
          (1 + 4 * s + 6 * s EXP 2)``;
