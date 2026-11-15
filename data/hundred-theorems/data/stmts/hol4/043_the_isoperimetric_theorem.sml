(*
  Statement-only formalization of Hundred Theorems corpus artifact
  hundred-theorems__hol4__043, cataloged as "The Isoperimetric Theorem":
  a rectifiable simple closed plane curve of length L encloses area at most
  L^2 / (4 * pi), with equality only when its image is a circle. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory real_sigmaTheory;
open transcTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val isoperimetric_theorem =
  ``!(L : real) (g : real -> real # real).
      let sqdist =
        \x y : real # real.
          (FST y - FST x) pow 2 + (SND y - SND x) pow 2
      in
      let on_unit_interval =
        \t. 0 <= t /\ t <= 1
      in
      let continuous_plane_path =
        \h.
          !t. on_unit_interval t ==>
              !e. 0 < e ==>
                  ?d. 0 < d /\
                      !s. on_unit_interval s /\ abs (s - t) < d ==>
                          sqdist (h s) (h t) < e
      in
      let path_image =
        \z. ?t. on_unit_interval t /\ g t = z
      in
      let partition =
        \n p.
          p 0 = 0 /\
          p n = 1 /\
          !i. i < n ==> p i < p (SUC i)
      in
      let polygonal_length =
        \n p.
          SIGMA
            (\i. sqrt (sqdist (g (p i)) (g (p (SUC i)))))
            (count n)
      in
      let path_length =
        \ell.
          0 <= ell /\
          (!n p.
             partition n p ==> polygonal_length n p <= ell) /\
          (!e. 0 < e ==>
               ?n p.
                 partition n p /\
                 ell - e < polygonal_length n p)
      in
      let rectifiable_path =
        (?ell. path_length ell)
      in
      let simple_path =
        (continuous_plane_path g /\
         !s t.
           on_unit_interval s /\
           on_unit_interval t /\
           g s = g t
           ==>
           s = t \/ (s = 0 /\ t = 1) \/ (s = 1 /\ t = 0))
      in
      let open_plane_set =
        \U : (real # real) -> bool.
          !x. U x ==>
              ?e. 0 < e /\
                  !y. sqdist x y < e ==> U y
      in
      let connected_plane_set =
        \C : (real # real) -> bool.
          ~(?U V : (real # real) -> bool.
              open_plane_set U /\
              open_plane_set V /\
              (?x. C x /\ U x) /\
              (?x. C x /\ V x) /\
              (!x. C x ==> U x \/ V x) /\
              (!x. C x ==> ~(U x /\ V x)))
      in
      let same_component =
        \x y : real # real.
          ?C : (real # real) -> bool.
            connected_plane_set C /\
            C x /\
            C y /\
            !z. C z ==> ~path_image z
      in
      let inside =
        \z : real # real.
          ~path_image z /\
          ?B : real.
            !w. same_component z w ==> sqdist (0, 0) w <= B
      in
      let enclosed_area =
        measure (prod_measure_space lebesgue lebesgue) inside
      in
        rectifiable_path /\
        simple_path /\
        g 1 = g 0 /\
        path_length L
        ==>
        enclosed_area <= Normal (L pow 2 / (4 * pi)) /\
        (enclosed_area = Normal (L pow 2 / (4 * pi))
         ==>
         ?c r.
           path_image =
             {z : real # real | sqdist c z = r pow 2})``;
