(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q318767 (thousand-theorems__hol4__Q318767), "Abel's theorem": a power
  series whose coefficient series converges at 1 tends to that sum within
  every positive Stolz cone, with the corresponding real left-limit
  statement. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val q318767_complex_partial_sum_def = new_definition (
  "q318767_complex_partial_sum_def",
  ``q318767_complex_partial_sum (f : num -> complex) n =
      ITSET (\i acc. f i + acc) (count n) (0 : complex)``);

val q318767_real_partial_sum_def = new_definition (
  "q318767_real_partial_sum_def",
  ``q318767_real_partial_sum (f : num -> real) n =
      ITSET (\i acc. f i + acc) (count n) (0 : real)``);

val q318767_complex_tendsto_seq_def = new_definition (
  "q318767_complex_tendsto_seq_def",
  ``q318767_complex_tendsto_seq (u : num -> complex) (l : complex) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> modu (u n - l) < epsilon``);

val q318767_real_tendsto_seq_def = new_definition (
  "q318767_real_tendsto_seq_def",
  ``q318767_real_tendsto_seq (u : num -> real) (l : real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> abs (u n - l) < epsilon``);

val q318767_complex_tsum_def = new_definition (
  "q318767_complex_tsum_def",
  ``q318767_complex_tsum (f : num -> complex) =
      if ?l : complex.
           q318767_complex_tendsto_seq
             (q318767_complex_partial_sum f) l
      then
        @l : complex.
          q318767_complex_tendsto_seq
            (q318767_complex_partial_sum f) l
      else 0``);

val q318767_real_tsum_def = new_definition (
  "q318767_real_tsum_def",
  ``q318767_real_tsum (f : num -> real) =
      if ?l : real.
           q318767_real_tendsto_seq
             (q318767_real_partial_sum f) l
      then
        @l : real.
          q318767_real_tendsto_seq
            (q318767_real_partial_sum f) l
      else 0``);

val q318767_stolz_cone_def = new_definition (
  "q318767_stolz_cone_def",
  ``q318767_stolz_cone (s : real) (z : complex) <=>
      abs (IM z) < s * (1 - RE z)``);

val Complex_tendsto_tsum_powerSeries_nhdsWithin_stolzCone =
  ``!(f : num -> complex) (l : complex) (s : real).
      q318767_complex_tendsto_seq
        (q318767_complex_partial_sum f) l /\
      0 < s
      ==>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !z : complex.
            q318767_stolz_cone s z /\
            modu (z - 1) < delta
            ==>
            modu
              (q318767_complex_tsum
                 (\n. f n * z pow n) -
               l) < epsilon``;

val Real_tendsto_tsum_powerSeries_nhdsWithin_lt =
  ``!(f : num -> real) (l : real).
      q318767_real_tendsto_seq
        (q318767_real_partial_sum f) l
      ==>
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !x : real.
            x < 1 /\
            abs (x - 1) < delta
            ==>
            abs
              (q318767_real_tsum
                 (\n. f n * x pow n) -
               l) < epsilon``;
