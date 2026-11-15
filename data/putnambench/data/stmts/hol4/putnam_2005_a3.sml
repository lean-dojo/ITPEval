(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a3:
  critical points of a normalized complex polynomial divided by its
  degree-dependent half-power lie on the unit circle when all polynomial
  zeros do. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val putnam_2005_a3 =
  ``!p : num -> complex. !n : num. !g : complex -> complex. !z : complex.
      0 < n /\
      p n <> 0 /\
      (!k : num. n < k ==> p k = 0) /\
      (!w : complex.
         ITSET
           (\k acc. p k * w pow k + acc)
           (count (SUC n))
           (0 : complex) = 0
         ==>
         modu w = 1) /\
      (!w : complex.
         g w =
           ITSET
             (\k acc. p k * w pow k + acc)
             (count (SUC n))
             (0 : complex) /
           (@r : complex.
              r pow 2 = w pow n /\
              0 <= RE r /\
              (RE r = 0 ==> 0 <= IM r))) /\
      z <> 0 /\
      (!e : real.
         0 < e
         ==>
         ?delta : real.
           0 < delta /\
           !w : complex.
             0 < modu (w - z) /\ modu (w - z) < delta
             ==>
             modu ((g w - g z) / (w - z)) < e)
      ==>
      modu z = 1``;
