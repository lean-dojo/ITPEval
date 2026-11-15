(*
  Statement-only formalization of PutnamBench artifact putnam_1975_b1:
  the integer span of (3,8), (4,-1), and (5,4) has a basis of the form
  (1,b), (0,7) for some integer b, with positive second generator.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pairTheory pred_setTheory;

val putnam_1975_b1 =
  ``let solution = 7 : int
    in
      !H : (int # int) set.
        H =
          {p : int # int |
             ?u v w : int.
               p =
                 (u * 3 + v * 4 + w * 5,
                  u * 8 - v + w * 4)}
        ==>
        (?b : int.
           H =
             {p : int # int |
                ?u v : int.
                  p = (u, u * b + v * solution)}) /\
        0 < solution``;
