(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1986_a5:
  a finite-dimensional real vector field with continuous second partial
  derivatives and constant antisymmetric first-partial differences admits a
  scalar correction whose components are linear. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory fcpTheory realTheory real_sigmaTheory;
open real_topologyTheory limTheory;

val putnam_1986_a5 =
  ``let xrepl =
      \x : real['N].
      \i : num.
      \xi : real.
        FCP k. if k = i then xi else x ' k
    in
    let partderiv =
      \func : real['N] -> real.
      \i : num.
      \x : real['N].
        diffn 1 (\xi : real. func (xrepl x i xi)) (x ' i)
    in
    let sqdist =
      \x y : real['N].
        REAL_SUM_IMAGE
          (\k : num. (x ' k - y ' k) pow 2)
          (count (dimindex (:'N)))
    in
    let euclidean_continuous =
      \h : real['N] -> real.
        !x : real['N].
        !e : real.
          0 < e
          ==>
          ?d : real.
            0 < d /\
            !y : real['N].
              sqdist x y < d ==> abs (h y - h x) < e
    in
    let has_continuous_second_partials =
      \func : real['N] -> real.
        (!i : num.
         !x : real['N].
           i < dimindex (:'N)
           ==>
           higher_differentiable
             1
             (\xi : real. func (xrepl x i xi))
             (x ' i)) /\
        (!i j : num.
         !x : real['N].
           i < dimindex (:'N) /\
           j < dimindex (:'N)
           ==>
           higher_differentiable
             1
             (\xj : real.
                partderiv func i (xrepl x j xj))
             (x ' j)) /\
        (!i j : num.
           i < dimindex (:'N) /\
           j < dimindex (:'N)
           ==>
           euclidean_continuous
             (\x : real['N].
                partderiv (partderiv func i) j x))
    in
    let addv =
      \x y : real['N].
        FCP k. x ' k + y ' k
    in
    let smulv =
      \a : real.
      \x : real['N].
        FCP k. a * x ' k
    in
    let is_linear =
      \h : real['N] -> real.
        (!x y : real['N].
           h (addv x y) = h x + h y) /\
        (!a : real.
         !x : real['N].
           h (smulv a x) = a * h x)
    in
      !n : num.
      !f : (real['N] -> real)['N].
        dimindex (:'N) = n /\
        0 < n /\
        (!i : num.
           i < n ==> has_continuous_second_partials (f ' i)) /\
        (?c : real['N]['N].
           !i j : num.
             i < n /\ j < n
             ==>
             !x : real['N].
               partderiv (f ' i) j x -
                 partderiv (f ' j) i x =
               c ' i ' j)
        ==>
        ?g : real['N] -> real.
          !i : num.
            i < n
            ==>
            is_linear
              (\x : real['N].
                 (f ' i) x + partderiv g i x)``;
