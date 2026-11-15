(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_a5:
  the impossibility of three consecutive equal blocks in the binary
  digit-parity sequence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_1992_a5 =
  ``!d : num -> num.
      (!n : num.
         d n =
         if n < 2 then n
         else n MOD 2 + d (n DIV 2))
      ==>
      let a =
        \n : num. if EVEN (d n) then 0 else 1
      in
        ~(?k m : num.
            0 < k /\
            0 < m /\
            !j : num.
              j <= m - 1
              ==>
              a (k + j) = a (k + m + j) /\
              a (k + m + j) = a (k + 2 * m + j))``;
