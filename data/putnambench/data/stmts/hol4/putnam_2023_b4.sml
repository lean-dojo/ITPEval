(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b4
  (putnambench__hol4__putnam_2023_b4): the least time for a piecewise
  twice-differentiable real function with prescribed accelerations and
  right-hand first-derivative limits to reach 2023 is 29. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_topologyTheory limTheory;

val putnam_2023_b4 =
  ``let right_limit =
      \g : real -> real. \a l : real.
        !e : real.
          0 < e
          ==>
          ?d : real.
            0 < d /\
            !x : real.
              a < x /\ x - a < d
              ==>
              abs (g x - l) < e
    in
    let regular =
      \n : num. \ts : num -> real. \t : real.
        ts 0 < t /\
        (!i : num.
           1 <= i /\ i <= n
           ==>
           t <> ts i)
    in
    let attainable =
      \T : real.
        0 <= T /\
        ?n : num. ?ts : num -> real. ?f fp : real -> real.
          (!k : num.
             k < n
             ==>
             ts k + 1 <= ts (k + 1)) /\
          f continuous_on {t : real | ts 0 <= t} /\
          (!t : real.
             regular n ts t
             ==>
             (f diffl (fp t)) t /\
             (?d : real. (fp diffl d) t)) /\
          f (ts 0) = 1 / 2 /\
          (!k : num.
             k <= n
             ==>
             right_limit fp (ts k) 0) /\
          (!k : num.
             k < n
             ==>
             !t : real.
               ts k < t /\ t < ts (k + 1)
               ==>
               (fp diffl &(k + 1)) t) /\
          (!t : real.
             ts n < t
             ==>
             (fp diffl &(n + 1)) t) /\
          f (ts 0 + T) = 2023
    in
      attainable 29 /\
      (!T : real.
         attainable T
         ==>
         29 <= T)``;
