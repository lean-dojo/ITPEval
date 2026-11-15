(*
  Statement-only formalization of "Green's Theorem" from Hundred Theorems item 021. This file
  contains no proof.
*)

(* Hundred Theorems, Green's Theorem (021): boundary circulation of a C1
   planar field around a positively oriented absolutely continuous closed
   path equals the area integral of its scalar curl. This is a statement-only
   formalization and contains no proof. *)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory transcTheory;
open limTheory integrationTheory;
open extrealTheory measureTheory lebesgueTheory lebesgue_measureTheory;
open martingaleTheory;

val green_s_theorem =
  ``!(P Q : (real # real) -> real)
      (g : real -> (real # real))
      (dg : real -> (real # real))
      (u : (real # real) -> bool)
      (dPdx dPdy dQdx dQdy : (real # real) -> real).
      let sqdist =
        \x y : real # real.
          (FST y - FST x) pow 2 + (SND y - SND x) pow 2
      in
      let on_unit_interval =
        \t. 0 <= t /\ t <= 1
      in
      let open_plane =
        \s : (real # real) -> bool.
          !x. s x ==>
              ?d. 0 < d /\
                  !y. sqdist x y < d pow 2 ==> s y
      in
      let continuous_on_plane =
        \s h.
          !x. s x ==>
              !e. 0 < e ==>
                  ?d. 0 < d /\
                      !y. s y /\ sqdist x y < d pow 2 ==>
                          abs (h y - h x) < e
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
      let path_derivative = dg
      in
      let absolutely_continuous_path =
        ((\t. FST (path_derivative t))
           absolutely_integrable_on interval [0, 1] /\
         (\t. SND (path_derivative t))
           absolutely_integrable_on interval [0, 1] /\
         !t. 0 <= t /\ t <= 1 ==>
             FST (g t) =
               FST (g 0) +
               integration$integral (interval [0, t])
                 (\s. FST (path_derivative s)) /\
             SND (g t) =
               SND (g 0) +
               integration$integral (interval [0, t])
                 (\s. SND (path_derivative s)))
      in
      let winding_integrand =
        \z t.
          ((FST (g t) - FST z) * SND (path_derivative t) -
           (SND (g t) - SND z) * FST (path_derivative t)) /
          sqdist z (g t)
      in
      let winding_number =
        \z.
          integration$integral (interval [0, 1])
            (winding_integrand z) / (2 * pi)
      in
      let same_component =
        \x y.
          ?h.
            continuous_plane_path h /\
            h 0 = x /\
            h 1 = y /\
            !t. on_unit_interval t ==> ~path_image (h t)
      in
      let unbounded_component =
        \z.
          ~path_image z /\
          !R. ?w.
            same_component z w /\
            R < sqrt (sqdist (0, 0) w)
      in
      let inside =
        \z. ~path_image z /\ ~unbounded_component z
      in
      let circulation =
        \t.
          P (g t) * FST (path_derivative t) +
          Q (g t) * SND (path_derivative t)
      in
      let area_density =
        \z.
          if inside z then Normal (dQdx z - dPdy z)
          else (0 : extreal)
      in
        absolutely_continuous_path /\
        g 1 = g 0 /\
        (!z. ~path_image z ==>
             winding_integrand z integrable_on interval [0, 1]) /\
        (!z. inside z ==> winding_number z = 1) /\
        open_plane u /\
        (!z. (inside z \/ path_image z) ==> u z) /\
        (!z. u z ==>
             ((\x. P (x, SND z)) diffl dPdx z) (FST z) /\
             ((\y. P (FST z, y)) diffl dPdy z) (SND z) /\
             ((\x. Q (x, SND z)) diffl dQdx z) (FST z) /\
             ((\y. Q (FST z, y)) diffl dQdy z) (SND z)) /\
        continuous_on_plane u dPdx /\
        continuous_on_plane u dPdy /\
        continuous_on_plane u dQdx /\
        continuous_on_plane u dQdy
        ==>
        lebesgue$integrable
          (prod_measure_space lebesgue lebesgue) area_density /\
        circulation integrable_on interval [0, 1] /\
        Normal
          (integration$integral (interval [0, 1]) circulation) =
        lebesgue$integral
          (prod_measure_space lebesgue lebesgue) area_density``;
