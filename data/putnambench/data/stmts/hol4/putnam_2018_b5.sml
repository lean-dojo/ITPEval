(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b5:
  a continuously differentiable map from the real plane to itself, with
  positive partial derivatives satisfying the stated Jacobian inequality
  everywhere, is injective. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory limTheory;

val putnam_2018_b5 =
  ``let partial_x =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 1 (\t : real. h (t, SND p)) (FST p)
    in
    let partial_y =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 1 (\t : real. h (FST p, t)) (SND p)
    in
    let plane_continuous =
      \g : (real # real) -> real.
        !p : real # real.
        !e : real.
          0 < e
          ==>
          ?d : real.
            0 < d /\
            !q : real # real.
              (FST q - FST p) pow 2 + (SND q - SND p) pow 2 < d
              ==>
              abs (g q - g p) < e
    in
    let continuously_partially_differentiable =
      \h : (real # real) -> real.
        (!p : real # real.
           higher_differentiable
             1
             (\t : real. h (t, SND p))
             (FST p) /\
           higher_differentiable
             1
             (\t : real. h (FST p, t))
             (SND p)) /\
        plane_continuous (partial_x h) /\
        plane_continuous (partial_y h)
    in
      !f : (real # real) -> (real # real).
        continuously_partially_differentiable (\p. FST (f p)) /\
        continuously_partially_differentiable (\p. SND (f p)) /\
        (!p : real # real.
           0 < partial_x (\q. FST (f q)) p /\
           0 < partial_y (\q. FST (f q)) p /\
           0 < partial_x (\q. SND (f q)) p /\
           0 < partial_y (\q. SND (f q)) p) /\
        (!p : real # real.
           0 <
             partial_x (\q. FST (f q)) p *
               partial_y (\q. SND (f q)) p -
             (1 / 4) *
               (partial_y (\q. FST (f q)) p +
                partial_x (\q. SND (f q)) p) pow 2)
        ==>
        INJ f UNIV UNIV``;
