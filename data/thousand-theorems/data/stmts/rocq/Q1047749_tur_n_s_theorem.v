(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1047749
  (thousand-theorems__rocq__Q1047749), "Turán's theorem": for positive r,
  a finite simple graph has the maximum number of edges among graphs on the
  same vertices with no clique of size r + 1 exactly when it is isomorphic to
  the canonical balanced r-partite Turán graph. This file contains no proof.
*)

From Stdlib Require Import List Arith Bool.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1047749_finite_type (A : Type) : Type := {
  q1047749_enum : list A;
  q1047749_enum_nodup : NoDup q1047749_enum;
  q1047749_enum_complete :
    forall x : A, In x q1047749_enum
}.

Arguments q1047749_enum {A} _.

Definition q1047749_card
    {A : Type} (F : q1047749_finite_type A) : nat :=
  length (q1047749_enum F).

Record q1047749_simple_graph (A : Type) : Type := {
  q1047749_adj : A -> A -> bool;
  q1047749_adj_sym :
    forall x y : A, q1047749_adj x y = q1047749_adj y x;
  q1047749_adj_irrefl :
    forall x : A, q1047749_adj x x = false
}.

Arguments q1047749_adj {A} _ _ _.

Fixpoint q1047749_count_neighbors
    {A : Type}
    (G : q1047749_simple_graph A)
    (v : A) (vertices : list A) : nat :=
  match vertices with
  | nil => 0
  | w :: rest =>
      (if q1047749_adj G v w then 1 else 0) +
      q1047749_count_neighbors G v rest
  end.

Fixpoint q1047749_count_edges_in
    {A : Type}
    (G : q1047749_simple_graph A)
    (vertices : list A) : nat :=
  match vertices with
  | nil => 0
  | v :: rest =>
      q1047749_count_neighbors G v rest +
      q1047749_count_edges_in G rest
  end.

Definition q1047749_edge_count
    {A : Type}
    (F : q1047749_finite_type A)
    (G : q1047749_simple_graph A) : nat :=
  q1047749_count_edges_in G (q1047749_enum F).

Definition q1047749_injective_on_initial_segment
    {A : Type} (k : nat) (f : nat -> A) : Prop :=
  forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    f i = f j ->
    i = j.

Definition q1047749_has_clique_of_size
    {A : Type}
    (G : q1047749_simple_graph A)
    (k : nat) : Prop :=
  exists f : nat -> A,
    q1047749_injective_on_initial_segment k f /\
    forall i j : nat,
      (i < k)%nat ->
      (j < k)%nat ->
      i <> j ->
      q1047749_adj G (f i) (f j) = true.

Definition q1047749_clique_free
    {A : Type}
    (G : q1047749_simple_graph A)
    (k : nat) : Prop :=
  ~ q1047749_has_clique_of_size G k.

Definition q1047749_is_turan_maximal
    {A : Type}
    (F : q1047749_finite_type A)
    (G : q1047749_simple_graph A)
    (r : nat) : Prop :=
  q1047749_clique_free G (S r) /\
  forall H : q1047749_simple_graph A,
    q1047749_clique_free H (S r) ->
    (q1047749_edge_count F H <= q1047749_edge_count F G)%nat.

Definition q1047749_nonempty_iso_turan_graph
    {A : Type}
    (F : q1047749_finite_type A)
    (G : q1047749_simple_graph A)
    (r : nat) : Prop :=
  exists label : A -> nat,
    (forall x : A,
      (label x < q1047749_card F)%nat) /\
    (forall x y : A,
      label x = label y -> x = y) /\
    (forall i : nat,
      (i < q1047749_card F)%nat ->
      exists x : A, label x = i) /\
    (forall x y : A,
      q1047749_adj G x y =
      negb
        (Nat.eqb
          (Nat.modulo (label x) r)
          (Nat.modulo (label y) r))).

Theorem isTuranMaximal_iff_nonempty_iso_turanGraph :
  forall (A : Type)
         (F : q1047749_finite_type A)
         (G : q1047749_simple_graph A)
         (r : nat),
    (0 < r)%nat ->
    (q1047749_is_turan_maximal F G r <->
     q1047749_nonempty_iso_turan_graph F G r).
Admitted.
