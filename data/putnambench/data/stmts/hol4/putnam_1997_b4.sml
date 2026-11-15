(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_b4:
  coefficients of powers of 1 + x + x^2 satisfy an alternating finite-sum
  bound between zero and one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_1997_b4 =
  ``!(a : num -> num -> int).
      let base =
        \i : num. if i <= 2 then 1 else 0
      in
      let multiply =
        \p q : num -> num.
          \n : num.
            SIGMA
              (\i : num. p i * q (n - i))
              (count (SUC n))
      in
      let one =
        \i : num. if i = 0 then 1 else 0
      in
        (!m n : num.
           a m n =
             int_of_num
               (FUNPOW
                  (\p : num -> num. multiply p base)
                  m
                  one
                  n))
        ==>
        !k : num.
          let alternating_sum =
            FOLDL
              (\acc : int. \i : num.
                 acc + (~1 : int) ** i * a (k - i) i)
              0
              (GENLIST
                 (\i : num. i)
                 (SUC ((2 * k) DIV 3)))
          in
            0 <= alternating_sum /\ alternating_sum <= 1``;
