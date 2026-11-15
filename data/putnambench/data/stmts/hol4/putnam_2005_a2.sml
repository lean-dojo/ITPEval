(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a2:
  the number of unit-step rook tours visiting every point of an n-by-3
  integer grid exactly once, starting at (1,1) and ending at (n,1).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2005_a2 =
  ``!n : num.
      0 < n
      ==>
      let S =
        {ab : int # int |
           1 <= FST ab /\ FST ab <= int_of_num n /\
           1 <= SND ab /\ SND ab <= 3}
      in
      let indices = IMAGE SUC (count (3 * n))
      in
      let unit =
        \ab : int # int. \cd : int # int.
          (FST ab = FST cd /\ ABS (SND cd - SND ab) = 1) \/
          (SND ab = SND cd /\ ABS (FST cd - FST ab) = 1)
      in
      let rooktour =
        \p : num -> int # int.
          (!P : int # int.
             P IN S
             ==>
             ?!i : num. i IN indices /\ p i = P) /\
          (!i : num.
             i IN IMAGE SUC (count (3 * n - 1))
             ==>
             unit (p i) (p (i + 1))) /\
          p 0 = (0, 0) /\
          (!i : num. 3 * n < i ==> p i = (0, 0))
      in
      let tours =
        {p : num -> int # int |
           rooktour p /\
           p 1 = (1, 1) /\
           p (3 * n) = (int_of_num n, 1)}
      in
        FINITE tours /\
        CARD tours = if n = 1 then 0 else 2 EXP (n - 2)``;
