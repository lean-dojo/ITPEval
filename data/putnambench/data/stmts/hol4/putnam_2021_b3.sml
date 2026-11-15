(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b3:
  every twice continuously differentiable real function on the plane has a
  prescribed off-center disk on which the integral of y*h_x - x*h_y vanishes.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory real_topologyTheory limTheory
     transcTheory integrationTheory;

val putnam_2021_b3 =
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
    let partial_xx =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 2 (\t : real. h (t, SND p)) (FST p)
    in
    let partial_xy =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 1
          (\t : real. partial_x h (FST p, t))
          (SND p)
    in
    let partial_yx =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 1
          (\t : real. partial_y h (t, SND p))
          (FST p)
    in
    let partial_yy =
      \h : (real # real) -> real.
      \p : real # real.
        diffn 2 (\t : real. h (FST p, t)) (SND p)
    in
    let plane_continuous =
      \g : (real # real) -> real.
        !p : real # real.
        !e : real.
          0 < e
          ==>
          ?delta : real.
            0 < delta /\
            !q : real # real.
              (FST q - FST p) pow 2 +
                (SND q - SND p) pow 2 < delta
              ==>
              abs (g q - g p) < e
    in
    let twice_continuously_differentiable =
      \h : (real # real) -> real.
        (!p : real # real.
           higher_differentiable
             2
             (\t : real. h (t, SND p))
             (FST p) /\
           higher_differentiable
             2
             (\t : real. h (FST p, t))
             (SND p) /\
           higher_differentiable
             1
             (\t : real. partial_x h (FST p, t))
             (SND p) /\
           higher_differentiable
             1
             (\t : real. partial_y h (t, SND p))
             (FST p)) /\
        plane_continuous h /\
        plane_continuous (partial_x h) /\
        plane_continuous (partial_y h) /\
        plane_continuous (partial_xx h) /\
        plane_continuous (partial_xy h) /\
        plane_continuous (partial_yx h) /\
        plane_continuous (partial_yy h)
    in
    let rho =
      \h : (real # real) -> real.
      \p : real # real.
        SND p * partial_x h p - FST p * partial_y h p
    in
    let disk_integral =
      \h : (real # real) -> real.
      \c : real # real.
      \r : real.
        integration$integral
          (interval [FST c - r, FST c + r])
          (\x : real.
             integration$integral
               (interval
                  [SND c - sqrt (r pow 2 - (x - FST c) pow 2),
                   SND c + sqrt (r pow 2 - (x - FST c) pow 2)])
               (\y : real. rho h (x, y)))
    in
      !h : (real # real) -> real.
        twice_continuously_differentiable h
        ==>
        !d r : real.
          0 < d /\ 0 < r /\ r < d
          ==>
          ?c : real # real.
            sqrt (FST c pow 2 + SND c pow 2) = d /\
            disk_integral h c r = 0``;
