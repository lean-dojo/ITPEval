(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a6:
  ten bijections of the integers whose finite nonempty compositions reach
  every integer from zero have at most 512 binary-exponent composites
  stabilizing any finite nonempty integer set. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1994_a6 =
  ``!(f : num -> int -> int)
     (mijcomp : num -> (num -> num) -> num -> int -> int)
     (F : (int -> int) set).
      (!k : num.
         k < 10
         ==>
         BIJ (f k) (UNIV : int set) (UNIV : int set)) /\
      (!n : int.
         ?m : num.
           1 <= m /\
           ?i : num -> num.
             (!j : num. j < m ==> i j < 10) /\
             mijcomp m i 0 0 = n) /\
      (!m : num.
         1 <= m
         ==>
         !i : num -> num. !j : num.
           j < m
           ==>
           mijcomp m i j =
             if j = m - 1 then
               f (i j)
             else
               \x : int. f (i j) (mijcomp m i (j + 1) x)) /\
      F =
        {g : int -> int |
           ?e : num -> num.
             (!k : num. k < 10 ==> (e k = 0 \/ e k = 1)) /\
             g =
               \x : int.
                 FUNPOW (f 0) (e 0)
                   (FUNPOW (f 1) (e 1)
                     (FUNPOW (f 2) (e 2)
                       (FUNPOW (f 3) (e 3)
                         (FUNPOW (f 4) (e 4)
                           (FUNPOW (f 5) (e 5)
                             (FUNPOW (f 6) (e 6)
                               (FUNPOW (f 7) (e 7)
                                 (FUNPOW (f 8) (e 8)
                                   (FUNPOW (f 9) (e 9) x))))))))))}
      ==>
      !A : int set.
        FINITE A /\ A <> {}
        ==>
        CARD {g : int -> int | g IN F /\ IMAGE g A = A} <= 512``;
