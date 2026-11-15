(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2006_b4:
  a k-dimensional real vector subspace contains at most 2^k vertices of the
  n-dimensional unit hypercube, and this bound is attained. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory fcpTheory realTheory;

val putnam_2006_b4 =
  ``!n k : num.
      dimindex (:'N) = n /\
      0 < n /\
      k <= n
      ==>
      let vzero = (FCP i. (0 : real)) : real['N]
      in
      let vadd =
        \(x : real['N]) (y : real['N]).
          FCP i. x ' i + y ' i
      in
      let smul =
        \(c : real) (x : real['N]).
          FCP i. c * x ' i
      in
      let lincomb =
        \(m : num) (coeff : num -> real) (vec : num -> real['N]).
          FOLDL
            (\acc i. vadd acc (smul (coeff i) (vec i)))
            vzero
            (GENLIST (\i. i) m)
      in
      let independent =
        \basis : real['N] list.
          !coeff : num -> real.
            lincomb (LENGTH basis) coeff (\i. EL i basis) = vzero
            ==>
            !i : num. i < LENGTH basis ==> coeff i = 0
      in
      let is_subspace =
        \V : real['N] set.
          vzero IN V /\
          (!x y : real['N].
             x IN V /\ y IN V ==> vadd x y IN V) /\
          (!c : real.
             !x : real['N].
               x IN V ==> smul c x IN V)
      in
      let has_dimension =
        \V : real['N] set.
        \d : num.
          ?basis : real['N] list.
            LENGTH basis = d /\
            ALL_DISTINCT basis /\
            (!i : num. i < d ==> EL i basis IN V) /\
            independent basis /\
            (!x : real['N].
               x IN V
               ==>
               ?coeff : num -> real.
                 lincomb d coeff (\i. EL i basis) = x)
      in
      let Z =
        {P : real['N] |
           !i : num.
             i < n ==> P ' i = 0 \/ P ' i = 1}
      in
        (?V : real['N] set.
           is_subspace V /\
           has_dimension V k /\
           CARD (Z INTER V) = 2 EXP k) /\
        (!V : real['N] set.
           is_subspace V /\
           has_dimension V k
           ==>
           CARD (Z INTER V) <= 2 EXP k)``;
