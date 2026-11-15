(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1987_a5:
  nonexistence of a continuously partially differentiable curl-free vector
  field on punctured three-space with a prescribed singular planar trace.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;
open real_topologyTheory limTheory;

val putnam_1987_a5 =
  ``let origin = (0, (0, 0)) : real # (real # real)
    in
    let coord =
      \v : real # (real # real).
      \i : num.
        if i = 0 then FST v
        else if i = 1 then FST (SND v)
        else SND (SND v)
    in
    let replace =
      \v : real # (real # real).
      \i : num.
      \t : real.
        if i = 0 then (t, (coord v 1, coord v 2))
        else if i = 1 then (coord v 0, (t, coord v 2))
        else (coord v 0, (coord v 1, t))
    in
    let component =
      \V : (real # (real # real)) -> (real # (real # real)).
      \i : num.
      \v : real # (real # real).
        coord (V v) i
    in
    let partderiv =
      \h : (real # (real # real)) -> real.
      \j : num.
      \v : real # (real # real).
        diffn 1 (\t : real. h (replace v j t)) (coord v j)
    in
    let sqdist =
      \v w : real # (real # real).
        (coord w 0 - coord v 0) pow 2 +
        (coord w 1 - coord v 1) pow 2 +
        (coord w 2 - coord v 2) pow 2
    in
    let continuous_on_punctured =
      \h : (real # (real # real)) -> real.
        !v : real # (real # real).
          v <> origin
          ==>
          !e : real.
            0 < e
            ==>
            ?d : real.
              0 < d /\
              !w : real # (real # real).
                w <> origin /\ sqdist v w < d
                ==>
                abs (h w - h v) < e
    in
    let has_continuous_partials =
      \V : (real # (real # real)) -> (real # (real # real)).
        !i j : num.
          i < 3 /\ j < 3
          ==>
          (!v : real # (real # real).
             v <> origin
             ==>
             higher_differentiable
               1
               (\t : real. component V i (replace v j t))
               (coord v j)) /\
          continuous_on_punctured (partderiv (component V i) j)
    in
    let curl_zero =
      \V : (real # (real # real)) -> (real # (real # real)).
        !v : real # (real # real).
          v <> origin
          ==>
          partderiv (component V 2) 1 v -
            partderiv (component V 1) 2 v = 0 /\
          partderiv (component V 0) 2 v -
            partderiv (component V 2) 0 v = 0 /\
          partderiv (component V 1) 0 v -
            partderiv (component V 0) 1 v = 0
    in
    let has_prescribed_trace =
      \V : (real # (real # real)) -> (real # (real # real)).
        !x y : real.
          V (x, (y, 0)) =
            (-y / (x pow 2 + 4 * y pow 2),
             (x / (x pow 2 + 4 * y pow 2), 0))
    in
      ((?V : (real # (real # real)) -> (real # (real # real)).
          has_continuous_partials V /\
          curl_zero V /\
          has_prescribed_trace V)
       <=> F)``;
