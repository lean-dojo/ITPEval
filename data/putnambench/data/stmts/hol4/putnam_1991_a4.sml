(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1991_a4:
  existence of closed disks in the real plane whose centers have no finite
  limit point, whose total area is finite, and which meet every line. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory realTheory real_sigmaTheory transcTheory;

val putnam_1991_a4 =
  ``let dist =
      \P Q : real # real.
        sqrt
          ((FST P - FST Q) pow 2 +
           (SND P - SND Q) pow 2)
    in
    let has_no_finite_limit_point =
      \c : num -> real # real.
        ~?p : real # real.
          !e : real.
            0 < e
            ==>
            ?f : num -> num.
              (!i j : num. i < j ==> f i < f j) /\
              !i : num. dist (c (f i)) p < e
    in
    let meets_every_line =
      \(c : num -> real # real) (r : num -> real).
        !v w : real # real.
          w <> (0, 0)
          ==>
          ?i : num. ?t : real.
            dist
              (FST v + t * FST w,
               SND v + t * SND w)
              (c i) <=
            r i
    in
    let putnam_1991_a4_solution = T
    in
      ((?c : num -> real # real. ?r : num -> real.
          (!i : num. 0 <= r i) /\
          has_no_finite_limit_point c /\
          summable (\i : num. (r i) pow 2) /\
          meets_every_line c r)
       <=>
       putnam_1991_a4_solution)``;
