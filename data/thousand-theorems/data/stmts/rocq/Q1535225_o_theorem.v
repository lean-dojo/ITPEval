(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1535225
  (thousand-theorems__rocq__Q1535225), "Łoś' theorem": a first-order sentence
  holds in an ultraproduct exactly when it holds in an ultrafilter-large set
  of the component structures. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1535225_language : Type := {
  q1535225_functions : nat -> Type;
  q1535225_relations : nat -> Type
}.

Inductive q1535225_tuple (A : Type) : nat -> Type :=
| q1535225_tuple_nil : q1535225_tuple A 0
| q1535225_tuple_cons :
    forall n, A -> q1535225_tuple A n -> q1535225_tuple A (S n).

Arguments q1535225_tuple_nil {A}.
Arguments q1535225_tuple_cons {A n} _ _.

Record q1535225_structure
    (L : q1535225_language) (A : Type) : Type := {
  q1535225_function_interpretation :
    forall n,
      q1535225_functions L n ->
      q1535225_tuple A n ->
      A;
  q1535225_relation_interpretation :
    forall n,
      q1535225_relations L n ->
      q1535225_tuple A n ->
      Prop
}.

Arguments q1535225_function_interpretation {L A} _ {n} _ _.
Arguments q1535225_relation_interpretation {L A} _ {n} _ _.

Inductive q1535225_term
    (L : q1535225_language) (variables : nat) : Type :=
| q1535225_variable :
    Fin.t variables ->
    q1535225_term L variables
| q1535225_function :
    forall arity,
      q1535225_functions L arity ->
      q1535225_terms L variables arity ->
      q1535225_term L variables
with q1535225_terms
    (L : q1535225_language) (variables : nat) : nat -> Type :=
| q1535225_terms_nil :
    q1535225_terms L variables 0
| q1535225_terms_cons :
    forall arity,
      q1535225_term L variables ->
      q1535225_terms L variables arity ->
      q1535225_terms L variables (S arity).

Arguments q1535225_variable {L variables} _.
Arguments q1535225_function {L variables arity} _ _.
Arguments q1535225_terms_nil {L variables}.
Arguments q1535225_terms_cons {L variables arity} _ _.

Fixpoint q1535225_term_denote
    {L : q1535225_language}
    {A : Type}
    {variables : nat}
    (M : q1535225_structure L A)
    (valuation : Fin.t variables -> A)
    (t : q1535225_term L variables) : A :=
  match t with
  | q1535225_variable index => valuation index
  | q1535225_function function_symbol arguments =>
      q1535225_function_interpretation M function_symbol
        (q1535225_terms_denote M valuation arguments)
  end
with q1535225_terms_denote
    {L : q1535225_language}
    {A : Type}
    {variables arity : nat}
    (M : q1535225_structure L A)
    (valuation : Fin.t variables -> A)
    (ts : q1535225_terms L variables arity) : q1535225_tuple A arity :=
  match ts with
  | q1535225_terms_nil => q1535225_tuple_nil
  | q1535225_terms_cons t rest =>
      q1535225_tuple_cons
        (q1535225_term_denote M valuation t)
        (q1535225_terms_denote M valuation rest)
  end.

Inductive q1535225_formula
    (L : q1535225_language) : nat -> Type :=
| q1535225_equal :
    forall variables,
      q1535225_term L variables ->
      q1535225_term L variables ->
      q1535225_formula L variables
| q1535225_atomic :
    forall variables arity,
      q1535225_relations L arity ->
      q1535225_terms L variables arity ->
      q1535225_formula L variables
| q1535225_falsum :
    forall variables, q1535225_formula L variables
| q1535225_implies :
    forall variables,
      q1535225_formula L variables ->
      q1535225_formula L variables ->
      q1535225_formula L variables
| q1535225_forall :
    forall variables,
      q1535225_formula L (S variables) ->
      q1535225_formula L variables.

Arguments q1535225_equal {L variables} _ _.
Arguments q1535225_atomic {L variables arity} _ _.
Arguments q1535225_falsum {L variables}.
Arguments q1535225_implies {L variables} _ _.
Arguments q1535225_forall {L variables} _.

Definition q1535225_extend_valuation
    {A : Type}
    {variables : nat}
    (x : A)
    (valuation : Fin.t variables -> A)
    (index : Fin.t (S variables)) : A :=
  Fin.caseS' index (fun _ => A) x valuation.

Fixpoint q1535225_satisfies
    {L : q1535225_language}
    {A : Type}
    {variables : nat}
    (M : q1535225_structure L A)
    (valuation : Fin.t variables -> A)
    (phi : q1535225_formula L variables) : Prop :=
  (match phi in q1535225_formula _ matched_variables
     return (Fin.t matched_variables -> A) -> Prop with
  | q1535225_equal t u =>
      fun matched_valuation =>
        q1535225_term_denote M matched_valuation t =
        q1535225_term_denote M matched_valuation u
  | q1535225_atomic relation_symbol arguments =>
      fun matched_valuation =>
        q1535225_relation_interpretation M relation_symbol
          (q1535225_terms_denote M matched_valuation arguments)
  | q1535225_falsum => fun _ => False
  | q1535225_implies psi chi =>
      fun matched_valuation =>
        q1535225_satisfies M matched_valuation psi ->
        q1535225_satisfies M matched_valuation chi
  | q1535225_forall psi =>
      fun matched_valuation =>
        forall x : A,
          q1535225_satisfies M
            (q1535225_extend_valuation x matched_valuation) psi
  end) valuation.

Definition q1535225_sentence
    (L : q1535225_language) : Type :=
  q1535225_formula L 0.

Definition q1535225_empty_valuation
    {A : Type} (index : Fin.t 0) : A :=
  match index with
  end.

Definition q1535225_sentence_satisfies
    {L : q1535225_language}
    {A : Type}
    (M : q1535225_structure L A)
    (phi : q1535225_sentence L) : Prop :=
  q1535225_satisfies M q1535225_empty_valuation phi.

Record q1535225_ultrafilter (I : Type) : Type := {
  q1535225_large : (I -> Prop) -> Prop;
  q1535225_large_universe :
    q1535225_large (fun _ => True);
  q1535225_large_upward :
    forall P Q : I -> Prop,
      (forall i : I, P i -> Q i) ->
      q1535225_large P ->
      q1535225_large Q;
  q1535225_large_intersection :
    forall P Q : I -> Prop,
      q1535225_large P ->
      q1535225_large Q ->
      q1535225_large (fun i => P i /\ Q i);
  q1535225_large_proper :
    ~ q1535225_large (fun _ => False);
  q1535225_large_or_complement :
    forall P : I -> Prop,
      q1535225_large P \/ q1535225_large (fun i => ~ P i)
}.

Arguments q1535225_large {I} _ _.

Definition q1535225_representative
    {I : Type} (A : I -> Type) : Type :=
  forall i : I, A i.

Fixpoint q1535225_ultraproduct_satisfies
    {I : Type}
    {L : q1535225_language}
    {A : I -> Type}
    {variables : nat}
    (M : forall i : I, q1535225_structure L (A i))
    (u : q1535225_ultrafilter I)
    (valuation :
      Fin.t variables -> q1535225_representative A)
    (phi : q1535225_formula L variables) : Prop :=
  (match phi in q1535225_formula _ matched_variables
     return
       (Fin.t matched_variables -> q1535225_representative A) -> Prop
   with
  | q1535225_equal t s =>
      fun matched_valuation =>
        q1535225_large u (fun i =>
          q1535225_term_denote (M i)
            (fun k => matched_valuation k i) t =
          q1535225_term_denote (M i)
            (fun k => matched_valuation k i) s)
  | q1535225_atomic relation_symbol arguments =>
      fun matched_valuation =>
        q1535225_large u (fun i =>
          q1535225_relation_interpretation (M i) relation_symbol
            (q1535225_terms_denote (M i)
              (fun k => matched_valuation k i) arguments))
  | q1535225_falsum => fun _ => False
  | q1535225_implies psi chi =>
      fun matched_valuation =>
        q1535225_ultraproduct_satisfies M u matched_valuation psi ->
        q1535225_ultraproduct_satisfies M u matched_valuation chi
  | q1535225_forall psi =>
      fun matched_valuation =>
        forall x : q1535225_representative A,
          q1535225_ultraproduct_satisfies M u
            (q1535225_extend_valuation x matched_valuation) psi
  end) valuation.

Definition q1535225_ultraproduct_sentence_satisfies
    {I : Type}
    {L : q1535225_language}
    {A : I -> Type}
    (M : forall i : I, q1535225_structure L (A i))
    (u : q1535225_ultrafilter I)
    (phi : q1535225_sentence L) : Prop :=
  q1535225_ultraproduct_satisfies
    M u q1535225_empty_valuation phi.

Theorem q1535225_los_theorem :
  forall (I : Type)
         (L : q1535225_language)
         (A : I -> Type)
         (M : forall i : I, q1535225_structure L (A i))
         (u : q1535225_ultrafilter I),
    (forall i : I, inhabited (A i)) ->
    forall phi : q1535225_sentence L,
      q1535225_ultraproduct_sentence_satisfies M u phi <->
      q1535225_large u
        (fun i => q1535225_sentence_satisfies (M i) phi).
Admitted.
