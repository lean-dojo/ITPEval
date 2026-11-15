(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q226014, "Poincaré recurrence theorem": for a conservative nonsingular
  self-map of a measure space and a null-measurable set, almost every point in
  the set returns to it infinitely often. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory;

val q226014_null_measurable_def = new_definition (
  "q226014_null_measurable_def",
  ``q226014_null_measurable (m : 'a m_space) (s : 'a set) <=>
      ?t.
        t IN measurable_sets m /\
        almost_everywhere m (\x. (x IN s <=> x IN t))``);

val q226014_conservative_def = new_definition (
  "q226014_conservative_def",
  ``q226014_conservative (m : 'a m_space) (f : 'a -> 'a) <=>
      measure_space m /\
      m_space m = UNIV /\
      f IN measurable
        (m_space m,measurable_sets m)
        (m_space m,measurable_sets m) /\
      (!t.
         t IN measurable_sets m /\ measure m t = 0 ==>
         measure m (PREIMAGE f t) = 0) /\
      (!t.
         t IN measurable_sets m /\ measure m t <> 0 ==>
         ?x k.
           x IN t /\
           k <> 0 /\
           FUNPOW f k x IN t)``);

val poincare_recurrence_theorem =
  ``!(m : 'a m_space) (f : 'a -> 'a) (s : 'a set).
      q226014_conservative m f /\
      q226014_null_measurable m s
      ==>
      almost_everywhere m
        (\x.
           x IN s ==>
           !N. ?n. N <= n /\ FUNPOW f n x IN s)``;
