(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q7432915, "Schroeder–Bernstein theorem for measurable spaces": measurable
  embeddings in both directions between two measurable spaces yield a
  measurable equivalence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory sigma_algebraTheory;

val q7432915_measurable_embedding_def = new_definition (
  "q7432915_measurable_embedding_def",
  ``q7432915_measurable_embedding
      (ma : ('a set) set) (mb : ('b set) set)
      (f : 'a -> 'b) <=>
      INJ f UNIV UNIV /\
      f IN measurable (UNIV,ma) (UNIV,mb) /\
      (!s. s IN ma ==> IMAGE f s IN mb)``);

val MeasurableEmbedding_schroederBernstein =
  ``!(ma : ('a set) set) (mb : ('b set) set)
      (f : 'a -> 'b) (g : 'b -> 'a).
      sigma_algebra (UNIV,ma) /\
      sigma_algebra (UNIV,mb) /\
      q7432915_measurable_embedding ma mb f /\
      q7432915_measurable_embedding mb ma g
      ==>
      ?(h : 'a -> 'b) (k : 'b -> 'a).
        (!x. k (h x) = x) /\
        (!y. h (k y) = y) /\
        h IN measurable (UNIV,ma) (UNIV,mb) /\
        k IN measurable (UNIV,mb) (UNIV,ma)``;
