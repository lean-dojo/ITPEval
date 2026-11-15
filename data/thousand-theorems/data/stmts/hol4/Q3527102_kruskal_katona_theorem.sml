(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527102, "Kruskal–Katona theorem": among uniform families of subsets of
  Fin n, a no-larger initial segment of colex has no larger lower shadow.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q3527102_colex_le_def = new_definition (
  "q3527102_colex_le_def",
  ``q3527102_colex_le (s : num set) (t : num set) <=>
      !a. a IN s /\ ~(a IN t) ==>
          ?b. b IN t /\ ~(b IN s) /\ a <= b``);

val q3527102_colex_lt_def = new_definition (
  "q3527102_colex_lt_def",
  ``q3527102_colex_lt (s : num set) (t : num set) <=>
      q3527102_colex_le s t /\ s <> t``);

val q3527102_uniform_family_def = new_definition (
  "q3527102_uniform_family_def",
  ``q3527102_uniform_family
      (n : num) (r : num) (family : (num set) set) <=>
      FINITE family /\
      !s. s IN family ==>
          FINITE s /\ s SUBSET count n /\ CARD s = r``);

val q3527102_is_colex_initial_segment_def = new_definition (
  "q3527102_is_colex_initial_segment_def",
  ``q3527102_is_colex_initial_segment
      (n : num) (r : num) (family : (num set) set) <=>
      q3527102_uniform_family n r family /\
      !s t.
        s IN family /\
        FINITE t /\
        t SUBSET count n /\
        CARD t = r /\
        q3527102_colex_lt t s
        ==>
        t IN family``);

val q3527102_shadow_def = new_definition (
  "q3527102_shadow_def",
  ``q3527102_shadow (family : (num set) set) =
      {t : num set |
         ?s a. s IN family /\ a IN s /\ t = s DELETE a}``);

val kruskal_katona =
  ``!n r : num. !family initial : (num set) set.
      q3527102_uniform_family n r family /\
      CARD initial <= CARD family /\
      q3527102_is_colex_initial_segment n r initial
      ==>
      CARD (q3527102_shadow initial) <=
      CARD (q3527102_shadow family)``;
