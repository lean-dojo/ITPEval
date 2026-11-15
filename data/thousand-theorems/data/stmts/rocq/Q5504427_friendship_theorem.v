(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5504427
  (thousand-theorems__rocq__Q5504427), "Friendship theorem": every finite
  nonempty simple graph in which each pair of distinct vertices has exactly
  one common neighbor has a vertex adjacent to every other vertex. This file
  contains no proof.
*)

From Stdlib Require Import Lists.List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q5504427_finite (V : Type) : Type := {
  q5504427_listing : list V;
  q5504427_listing_nodup : NoDup q5504427_listing;
  q5504427_listing_complete :
    forall x : V, In x q5504427_listing
}.

Record q5504427_simple_graph (V : Type) : Type := {
  q5504427_adj : V -> V -> Prop;
  q5504427_adj_symmetric :
    forall x y : V, q5504427_adj x y -> q5504427_adj y x;
  q5504427_adj_irreflexive :
    forall x : V, ~ q5504427_adj x x
}.

Arguments q5504427_adj {V} _ _ _.

Module Theorems100.

Definition Friendship
    {V : Type}
    (G : q5504427_simple_graph V) : Prop :=
  forall v w : V,
    v <> w ->
    exists common : V,
      q5504427_adj G v common /\
      q5504427_adj G w common /\
      forall other : V,
        q5504427_adj G v other ->
        q5504427_adj G w other ->
        other = common.

Definition ExistsPolitician
    {V : Type}
    (G : q5504427_simple_graph V) : Prop :=
  exists politician : V,
    forall other : V,
      politician <> other ->
      q5504427_adj G politician other.

Theorem friendship_theorem :
  forall (V : Type)
         (_ : q5504427_finite V)
         (G : q5504427_simple_graph V),
    (exists vertex : V, True) ->
    Friendship G ->
    ExistsPolitician G.
Admitted.

End Theorems100.
