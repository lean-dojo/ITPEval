(*
  Statement-only formalization of Thousand Theorems artifact Q1032886
  (thousand-theorems__rocq__Q1032886), "Hales–Jewett theorem": for every
  finite alphabet and finite set of colors, some finite-dimensional word
  space has a monochromatic nondegenerate combinatorial line.
  This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.

Record FiniteWitness (A : Type) : Type := {
  finite_enumeration : list A;
  finite_enumeration_complete :
    forall x : A, In x finite_enumeration
}.

Record CombinatorialLine (A I : Type) : Type := {
  line_coordinates : I -> option A;
  line_nondegenerate :
    exists i : I, line_coordinates i = None
}.

Definition line_word
    {A I : Type} (line : CombinatorialLine A I) (x : A) (i : I) : A :=
  match @line_coordinates A I line i with
  | Some a => a
  | None => x
  end.

Theorem hales_jewett_theorem :
  forall (A K : Type),
    FiniteWitness A ->
    FiniteWitness K ->
    exists (I : Type),
      exists _ : FiniteWitness I,
        forall coloring : (I -> A) -> K,
          exists line : CombinatorialLine A I,
            exists color : K,
              forall x : A, coloring (line_word line x) = color.
Admitted.
