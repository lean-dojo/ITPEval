(*
  Statement-only formalization of Thousand Theorems corpus artifact Q510197
  (thousand-theorems__rocq__Q510197), "Tutte theorem": a finite simple graph
  has a perfect matching if and only if deleting any set of vertices leaves
  at most that many connected components of odd cardinality. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q510197_finite (V : Type) : Type := {
  q510197_listing : list V;
  q510197_listing_nodup : NoDup q510197_listing;
  q510197_listing_complete :
    forall x : V, In x q510197_listing
}.

Record q510197_simple_graph (V : Type) : Type := {
  q510197_adj : V -> V -> Prop;
  q510197_adj_symmetric :
    forall x y : V, q510197_adj x y -> q510197_adj y x;
  q510197_adj_irreflexive :
    forall x : V, ~ q510197_adj x x
}.

Arguments q510197_adj {V} _ _ _.

Definition q510197_is_subgraph
    {V : Type}
    (M G : q510197_simple_graph V) : Prop :=
  forall x y : V, q510197_adj M x y -> q510197_adj G x y.

Definition q510197_is_perfect_matching
    {V : Type}
    (G M : q510197_simple_graph V) : Prop :=
  q510197_is_subgraph M G /\
  forall x : V,
    exists y : V,
      q510197_adj M x y /\
      forall z : V, q510197_adj M x z -> z = y.

Inductive q510197_reachable_without
    {V : Type}
    (G : q510197_simple_graph V)
    (deleted : V -> Prop) : V -> V -> Prop :=
| q510197_reachable_refl :
    forall x : V,
      ~ deleted x ->
      q510197_reachable_without G deleted x x
| q510197_reachable_step :
    forall x y z : V,
      ~ deleted x ->
      q510197_adj G x y ->
      q510197_reachable_without G deleted y z ->
      q510197_reachable_without G deleted x z.

Definition q510197_set_cardinality
    {V : Type}
    (S : V -> Prop)
    (n : nat) : Prop :=
  exists xs : list V,
    NoDup xs /\
    (forall x : V, S x <-> In x xs) /\
    length xs = n.

Definition q510197_odd (n : nat) : Prop :=
  exists k : nat, n = S (2 * k).

Definition q510197_is_odd_component
    {V : Type}
    (G : q510197_simple_graph V)
    (deleted : V -> Prop)
    (root : V) : Prop :=
  ~ deleted root /\
  exists n : nat,
    q510197_set_cardinality
      (fun x : V => q510197_reachable_without G deleted root x) n /\
    q510197_odd n.

Definition q510197_pairwise_distinct_components
    {V : Type}
    (G : q510197_simple_graph V)
    (deleted : V -> Prop)
    (representatives : list V) : Prop :=
  forall x y : V,
    In x representatives ->
    In y representatives ->
    x <> y ->
    ~ q510197_reachable_without G deleted x y.

Definition q510197_odd_components_cardinality
    {V : Type}
    (G : q510197_simple_graph V)
    (deleted : V -> Prop)
    (n : nat) : Prop :=
  exists representatives : list V,
    NoDup representatives /\
    (forall root : V,
      In root representatives ->
      q510197_is_odd_component G deleted root) /\
    q510197_pairwise_distinct_components G deleted representatives /\
    (forall root : V,
      q510197_is_odd_component G deleted root ->
      exists representative : V,
        In representative representatives /\
        q510197_reachable_without G deleted root representative) /\
    length representatives = n.

Definition q510197_is_tutte_violator
    {V : Type}
    (G : q510197_simple_graph V)
    (deleted : V -> Prop) : Prop :=
  exists removed_count odd_component_count : nat,
    q510197_set_cardinality deleted removed_count /\
    q510197_odd_components_cardinality
      G deleted odd_component_count /\
    removed_count < odd_component_count.

Definition q510197_tutte_condition
    {V : Type}
    (_ : q510197_finite V)
    (G : q510197_simple_graph V) : Prop :=
  forall deleted : V -> Prop,
    ~ q510197_is_tutte_violator G deleted.

Module SimpleGraph.

Theorem tutte :
  forall (V : Type)
         (finite_vertices : q510197_finite V)
         (G : q510197_simple_graph V),
    (exists M : q510197_simple_graph V,
      q510197_is_perfect_matching G M) <->
    q510197_tutte_condition finite_vertices G.
Admitted.

End SimpleGraph.
