(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_a5:
  a bound for pairwise values of a twice continuously differentiable real
  function whose gradient is governed by a positive decaying function. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;
open real_topologyTheory limTheory;

val putnam_2011_a5 =
  ``let continuous2 =
      \h : real -> real -> real.
        !u v e : real.
          0 < e
          ==>
          ?d : real.
            0 < d /\
            !x y : real.
              (x - u) pow 2 + (y - v) pow 2 < d
              ==>
              abs (h x y - h u v) < e
    in
    let du =
      \F : real -> real -> real.
      \u v : real.
        diffn 1 (\x : real. F x v) u
    in
    let dv =
      \F : real -> real -> real.
      \u v : real.
        diffn 1 (F u) v
    in
    let duu =
      \F : real -> real -> real.
      \u v : real.
        diffn 2 (\x : real. F x v) u
    in
    let duv =
      \F : real -> real -> real.
      \u v : real.
        diffn 1 (\y : real. du F u y) v
    in
    let dvu =
      \F : real -> real -> real.
      \u v : real.
        diffn 1 (\x : real. dv F x v) u
    in
    let dvv =
      \F : real -> real -> real.
      \u v : real.
        diffn 2 (F u) v
    in
    let twice_continuously_differentiable =
      \h : real -> real.
        (!x : real. higher_differentiable 2 h x) /\
        (diffn 1 h) continuous_on UNIV /\
        (diffn 2 h) continuous_on UNIV
    in
    let twice_continuously_differentiable2 =
      \F : real -> real -> real.
        (!u v : real.
           higher_differentiable 2 (\x : real. F x v) u /\
           higher_differentiable 2 (F u) v /\
           higher_differentiable 1 (\y : real. du F u y) v /\
           higher_differentiable 1 (\x : real. dv F x v) u) /\
        continuous2 (du F) /\
        continuous2 (dv F) /\
        continuous2 (duu F) /\
        continuous2 (duv F) /\
        continuous2 (dvu F) /\
        continuous2 (dvv F)
    in
      !F : real -> real -> real.
      !g : real -> real.
        twice_continuously_differentiable2 F /\
        twice_continuously_differentiable g /\
        (!u : real. F u u = 0) /\
        (!x : real. 0 < g x /\ x pow 2 * g x <= 1) /\
        (!u v : real.
           ?c : real.
             du F u v = c * g u /\
             dv F u v = c * -g v)
        ==>
        ?C : real.
          !n : num.
            2 <= n
            ==>
            !x : num -> real.
              ?i j : num.
                i <= n /\ j <= n /\ i <> j /\
                abs (F (x i) (x j)) <= C / &n``;
