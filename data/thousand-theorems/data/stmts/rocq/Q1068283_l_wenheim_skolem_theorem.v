(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1068283
  (thousand-theorems__rocq__Q1068283), "Löwenheim–Skolem theorem": for every
  infinite cardinal at least the language cardinality, an infinite first-order
  structure has a structure of that cardinality with an elementary embedding
  in one direction. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1068283_language : Type := {
  q1068283_functions : nat -> Type;
  q1068283_relations : nat -> Type
}.

Inductive q1068283_tuple (A : Type) : nat -> Type :=
| q1068283_tuple_nil : q1068283_tuple A 0
| q1068283_tuple_cons :
    forall n, A -> q1068283_tuple A n -> q1068283_tuple A (S n).

Arguments q1068283_tuple_nil {A}.
Arguments q1068283_tuple_cons {A n} _ _.

Record q1068283_structure (L : q1068283_language) (A : Type) : Type := {
  q1068283_function_interpretation :
    forall n,
      q1068283_functions L n ->
      q1068283_tuple A n ->
      A;
  q1068283_relation_interpretation :
    forall n,
      q1068283_relations L n ->
      q1068283_tuple A n ->
      Prop
}.

Arguments q1068283_function_interpretation {L A} _ {n} _ _.
Arguments q1068283_relation_interpretation {L A} _ {n} _ _.

Inductive q1068283_term (L : q1068283_language) : Type :=
| q1068283_variable : nat -> q1068283_term L
| q1068283_function :
    forall n,
      q1068283_functions L n ->
      q1068283_terms L n ->
      q1068283_term L
with q1068283_terms (L : q1068283_language) : nat -> Type :=
| q1068283_terms_nil : q1068283_terms L 0
| q1068283_terms_cons :
    forall n,
      q1068283_term L ->
      q1068283_terms L n ->
      q1068283_terms L (S n).

Arguments q1068283_variable {L} _.
Arguments q1068283_function {L n} _ _.
Arguments q1068283_terms_nil {L}.
Arguments q1068283_terms_cons {L n} _ _.

Fixpoint q1068283_term_denote
    {L : q1068283_language}
    {A : Type}
    (S : q1068283_structure L A)
    (valuation : nat -> A)
    (t : q1068283_term L) : A :=
  match t with
  | q1068283_variable k => valuation k
  | q1068283_function f ts =>
      q1068283_function_interpretation S f
        (q1068283_terms_denote S valuation ts)
  end
with q1068283_terms_denote
    {L : q1068283_language}
    {A : Type}
    (S : q1068283_structure L A)
    (valuation : nat -> A)
    {n : nat}
    (ts : q1068283_terms L n) : q1068283_tuple A n :=
  match ts with
  | q1068283_terms_nil => q1068283_tuple_nil
  | q1068283_terms_cons t rest =>
      q1068283_tuple_cons
        (q1068283_term_denote S valuation t)
        (q1068283_terms_denote S valuation rest)
  end.

Inductive q1068283_formula (L : q1068283_language) : Type :=
| q1068283_equal :
    q1068283_term L -> q1068283_term L -> q1068283_formula L
| q1068283_atomic :
    forall n,
      q1068283_relations L n ->
      q1068283_terms L n ->
      q1068283_formula L
| q1068283_falsum : q1068283_formula L
| q1068283_implies :
    q1068283_formula L -> q1068283_formula L -> q1068283_formula L
| q1068283_forall : q1068283_formula L -> q1068283_formula L.

Arguments q1068283_equal {L} _ _.
Arguments q1068283_atomic {L n} _ _.
Arguments q1068283_falsum {L}.
Arguments q1068283_implies {L} _ _.
Arguments q1068283_forall {L} _.

Definition q1068283_extend_valuation
    {A : Type} (x : A) (valuation : nat -> A) : nat -> A :=
  fun k =>
    match k with
    | 0 => x
    | S j => valuation j
    end.

Fixpoint q1068283_satisfies
    {L : q1068283_language}
    {A : Type}
    (S : q1068283_structure L A)
    (valuation : nat -> A)
    (phi : q1068283_formula L) : Prop :=
  match phi with
  | q1068283_equal t u =>
      q1068283_term_denote S valuation t =
      q1068283_term_denote S valuation u
  | q1068283_atomic r ts =>
      q1068283_relation_interpretation S r
        (q1068283_terms_denote S valuation ts)
  | q1068283_falsum => False
  | q1068283_implies psi chi =>
      q1068283_satisfies S valuation psi ->
      q1068283_satisfies S valuation chi
  | q1068283_forall psi =>
      forall x : A,
        q1068283_satisfies S
          (q1068283_extend_valuation x valuation) psi
  end.

Definition q1068283_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q1068283_surjective
    {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition q1068283_card_le (A B : Type) : Prop :=
  exists f : A -> B, q1068283_injective f.

Definition q1068283_same_cardinality (A B : Type) : Prop :=
  exists f : A -> B,
    q1068283_injective f /\ q1068283_surjective f.

Definition q1068283_infinite (A : Type) : Prop :=
  ~ exists enumeration : list A,
      forall x : A, In x enumeration.

Definition q1068283_symbols (L : q1068283_language) : Type :=
  ({ n : nat & q1068283_functions L n } +
   { n : nat & q1068283_relations L n })%type.

Definition q1068283_elementary_embedding
    {L : q1068283_language}
    {A B : Type}
    (SA : q1068283_structure L A)
    (SB : q1068283_structure L B)
    (f : A -> B) : Prop :=
  q1068283_injective f /\
  forall (phi : q1068283_formula L) (valuation : nat -> A),
    q1068283_satisfies SA valuation phi <->
    q1068283_satisfies SB (fun k => f (valuation k)) phi.

Theorem q1068283_lowenheim_skolem :
  forall (L : q1068283_language)
         (M : Type)
         (K : Type)
         (SM : q1068283_structure L M),
    q1068283_infinite M ->
    q1068283_card_le nat K ->
    q1068283_card_le (q1068283_symbols L) K ->
    exists (N : Type) (SN : q1068283_structure L N),
      ((exists f : N -> M,
          q1068283_elementary_embedding SN SM f) \/
       (exists f : M -> N,
          q1068283_elementary_embedding SM SN f)) /\
      q1068283_same_cardinality N K.
Admitted.
