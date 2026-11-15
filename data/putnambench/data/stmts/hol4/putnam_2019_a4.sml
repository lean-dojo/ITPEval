(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a4:
  the assertion that every continuous real-valued function on real
  three-space with zero surface integral over every unit sphere is identically
  zero has the negative answer. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory real_sigmaTheory transcTheory
     integrationTheory;

val putnam_2019_a4 =
  ``let sqdist =
      \p q : real # (real # real).
        (FST q - FST p) pow 2 +
        (FST (SND q) - FST (SND p)) pow 2 +
        (SND (SND q) - SND (SND p)) pow 2
    in
    let continuous3 =
      \f : (real # (real # real)) -> real.
        !p : real # (real # real).
        !e : real.
          0 < e
          ==>
          ?d : real.
            0 < d /\
            !q : real # (real # real).
              sqdist p q < d ==> abs (f q - f p) < e
    in
    let unit_sphere_integral =
      \f : (real # (real # real)) -> real.
      \c : real # (real # real).
        integration$integral (interval [0, 2 * pi])
          (\theta : real.
             integration$integral (interval [0, pi])
               (\phi : real.
                  f
                    (FST c + sin phi * cos theta,
                     (FST (SND c) + sin phi * sin theta,
                      SND (SND c) + cos phi)) *
                  sin phi))
    in
      ((!f : (real # (real # real)) -> real.
          continuous3 f
          ==>
          (!c : real # (real # real). unit_sphere_integral f c = 0)
          ==>
          f = (\p : real # (real # real). 0))
       <=>
       F)``;
