(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__092, cataloged as "Pick's Theorem": the area
  enclosed by a simple closed lattice polygon equals its number of interior
  lattice points plus half its boundary lattice points minus one. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory intrealTheory listTheory pairTheory;
open pred_setTheory realTheory real_sigmaTheory;
open extrealTheory measureTheory lebesgue_measureTheory martingaleTheory;

val pick_s_theorem =
  ``!(g : real -> real # real) (vertices : (real # real) list).
      let sqdist =
        \x y : real # real.
          (FST y - FST x) pow 2 + (SND y - SND x) pow 2
      in
      let on_unit_interval =
        \t. 0 <= t /\ t <= 1
      in
      let edge_parameter =
        \i t. &(PRE (LENGTH vertices)) * t - &i
      in
      let polygonal_from_vertices =
        \h.
          2 <= LENGTH vertices /\
          !i t.
            SUC i < LENGTH vertices /\
            &i / &(PRE (LENGTH vertices)) <= t /\
            t <= &(SUC i) / &(PRE (LENGTH vertices))
            ==>
            FST (h t) =
              (1 - edge_parameter i t) * FST (EL i vertices) +
              edge_parameter i t * FST (EL (SUC i) vertices) /\
            SND (h t) =
              (1 - edge_parameter i t) * SND (EL i vertices) +
              edge_parameter i t * SND (EL (SUC i) vertices)
      in
      let continuous_plane_path =
        \h.
          !t. on_unit_interval t ==>
              !e. 0 < e ==>
                  ?d. 0 < d /\
                      !s. on_unit_interval s /\ abs (s - t) < d ==>
                          sqdist (h s) (h t) < e
      in
      let simple_path =
        \h.
          continuous_plane_path h /\
          !s t.
            on_unit_interval s /\
            on_unit_interval t /\
            h s = h t
            ==>
            s = t \/ (s = 0 /\ t = 1) \/ (s = 1 /\ t = 0)
      in
      let path_image =
        \z. ?t. on_unit_interval t /\ g t = z
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
      let integral_point =
        \z : real # real.
          (?m : int. FST z = real_of_int m) /\
          (?n : int. SND z = real_of_int n)
      in
        (!z. MEM z vertices ==> integral_point z) /\
        polygonal_from_vertices g /\
        simple_path g /\
        g 1 = g 0
        ==>
        measure (prod_measure_space lebesgue lebesgue) inside =
          Normal
            (&(CARD {z : real # real | inside z /\ integral_point z}) +
             &(CARD {z : real # real | path_image z /\ integral_point z}) /
               2 -
             1)``;
