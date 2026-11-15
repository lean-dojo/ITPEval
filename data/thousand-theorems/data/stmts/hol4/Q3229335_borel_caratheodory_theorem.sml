(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3229335 (thousand-theorems__hol4__Q3229335), "Borel–Carathéodory theorem":
  a complex-differentiable function on an open disk whose real part is
  bounded above satisfies the Borel–Carathéodory norm estimate there.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory complexTheory;

val q3229335_in_open_disk_def = new_definition (
  "q3229335_in_open_disk_def",
  ``q3229335_in_open_disk (R : real) (z : complex) <=>
      modu z < R``);

val q3229335_complex_differentiable_on_disk_def = new_definition (
  "q3229335_complex_differentiable_on_disk_def",
  ``q3229335_complex_differentiable_on_disk
      (f : complex -> complex) (R : real) <=>
      !x : complex.
        q3229335_in_open_disk R x ==>
        ?deriv : complex.
          !epsilon : real.
            0 < epsilon ==>
            ?delta : real.
              0 < delta /\
              !h : complex.
                0 < modu h /\ modu h < delta
                ==>
                modu (f (x + h) - f x - h * deriv) <
                  epsilon * modu h``);

val q3229335_maps_real_part_below_def = new_definition (
  "q3229335_maps_real_part_below_def",
  ``q3229335_maps_real_part_below
      (f : complex -> complex) (R : real) (M : real) <=>
      !x : complex.
        q3229335_in_open_disk R x ==>
        RE (f x) <= M``);

val borelCaratheodory =
  ``!(f : complex -> complex) (M : real) (R : real) (z : complex).
      0 < M /\
      q3229335_complex_differentiable_on_disk f R /\
      q3229335_maps_real_part_below f R M /\
      0 < R /\
      q3229335_in_open_disk R z
      ==>
      modu (f z) <=
        2 * M * modu z / (R - modu z) +
        modu (f 0) * (R + modu z) / (R - modu z)``;
