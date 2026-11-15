(*
  Statement-only formalization of PutnamBench artifact putnam_1989_b6:
  the expected right-endpoint Riemann sum over the ordered unit simplex is
  represented by integration against a bounded degree-n polynomial.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory fcpTheory realTheory;
open real_sigmaTheory real_topologyTheory integrationTheory polyTheory;

val putnam_1989_b6 =
  ``let xrepl =
      \x : real['N].
      \i : num.
      \t : real.
        FCP k. if k = i then t else x ' k
    in
    let cube_integral =
      \n : num.
      \g : real['N] -> real.
        FOLDL
          (\J : (real['N] -> real) -> real.
           \i : num.
           \h : real['N] -> real.
             integration$integral (interval [0, 1])
               (\t : real.
                  J (\x : real['N]. h (xrepl x i t))))
          (\h : real['N] -> real. h (FCP i. 0))
          (GENLIST (\i : num. i) n)
          g
    in
    let ordered =
      \n : num.
      \x : real['N].
        (!i : num.
           i < n ==> 0 < x ' i /\ x ' i < 1) /\
        (!i : num.
           SUC i < n ==> x ' i < x ' (SUC i))
    in
    let xext =
      \n : num.
      \x : real['N].
      \i : num.
        if i = 0 then 0
        else if i = n + 1 then 1
        else x ' (i - 1)
    in
    let rsum =
      \n : num.
      \f : real -> real.
      \x : real['N].
        SIGMA
          (\i : num.
             (xext n x (i + 1) - xext n x i) *
             f (xext n x (i + 1)))
          (count (n + 1))
    in
      !n : num.
        0 < n /\
        dimindex (:'N) = n
        ==>
        ?P : real list.
          degree P = n /\
          (!t : real.
             t IN interval [0, 1]
             ==>
             0 <= poly P t /\ poly P t <= 1) /\
          !f : real -> real.
            f continuous_on interval [0, 1] /\
            f 1 = 0
            ==>
            cube_integral n
              (\x : real['N].
                 if ordered n x then rsum n f x else 0) /
              cube_integral n
                (\x : real['N].
                   if ordered n x then 1 else 0) =
            integration$integral (interval [0, 1])
              (\t : real. f t * poly P t)``;
