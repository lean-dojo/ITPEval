(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_a3:
  a bounded continuously partially differentiable real function on the plane
  satisfying a constant-coefficient first-order PDE is identically zero. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory limTheory;

val putnam_2010_a3 =
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
      !h : (real # real) -> real.
      !a b M : real.
        continuously_partially_differentiable h /\
        (!p : real # real.
           h p = a * partial_x h p + b * partial_y h p) /\
        (!p : real # real. abs (h p) <= M)
        ==>
        h = (\p : real # real. 0)``;
