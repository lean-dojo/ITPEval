(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_b5:
  a 2n by n complex matrix whose left kernel contains no nonzero real vector
  maps complex n-vectors onto all real 2n-vectors after taking real parts.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val putnam_1987_b5 =
  ``let complex_sum =
      \(s : num set) (f : num -> complex).
        ITSET (\i acc. f i + acc) s (0 : complex)
    in
      !n : num. !M : num -> num -> complex.
        0 < n /\
        (!z : num -> complex.
           (!j : num.
              j < n
              ==>
              complex_sum
                (count (2 * n))
                (\i : num. z i * M i j) = 0)
           ==>
           ~(!i : num. i < 2 * n ==> z i = 0)
           ==>
           ?i : num. i < 2 * n /\ IM (z i) <> 0)
        ==>
        !r : num -> real.
          ?w : num -> complex.
            !i : num.
              i < 2 * n
              ==>
              RE
                (complex_sum
                   (count n)
                   (\j : num. M i j * w j)) = r i``;
