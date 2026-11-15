(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a6:
  the reciprocal series defined by the base-b digit-length recurrence converges
  exactly for base 2 among natural-number bases at least 2. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_2002_a6 =
  ``let digitlength =
      \b n : num.
        if b < 2 then 0
        else LEAST k : num. n < b EXP k
    in
      !f : num -> num -> real.
        (!b : num.
           f b 1 = 1 /\
           f b 2 = 2 /\
           (!n : num.
              3 <= n
              ==>
              f b n = &n * f b (digitlength b n)))
        ==>
        {b : num |
           2 <= b /\
           ?L : real.
             ((\m : num.
                 SIGMA
                   (\n : num. 1 / f b n)
                   (IMAGE SUC (count m))) --> L)
             sequentially} =
        {b : num | b = 2}``;
