(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b1:
  no three consecutive coefficients vanish in a real power series agreeing
  near zero with the sum of x^n (x - 1)^(2n) / n!. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_1972_b1 =
  ``!S : real -> real. !p : num -> real.
      S =
        (\x : real.
           if
             summable
               (\n : num.
                  x pow n * (x - 1) pow (2 * n) / &(FACT n))
           then
             suminf
               (\n : num.
                  x pow n * (x - 1) pow (2 * n) / &(FACT n))
           else
             0) /\
      (?a : real.
         0 < a /\
         !x : real.
           abs x < a
           ==>
           (if summable (\n : num. p n * x pow n) then
              suminf (\n : num. p n * x pow n)
            else
              0) =
           S x)
      ==>
      ~?n : num.
         p n = 0 /\
         p (n + 1) = 0 /\
         p (n + 2) = 0``;
