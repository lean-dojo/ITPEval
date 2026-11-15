(*
  Statement-only formalization of Thousand Theorems corpus artifact Q422187
  (thousand-theorems__rocq__Q422187), "Myhill–Nerode theorem": a language over
  an arbitrary alphabet is regular if and only if its family of left quotients
  by finite words is finite. This file contains no proof.
*)

From Stdlib Require Import List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Module Q422187_MyhillNerode.

Definition q422187_language (Alphabet : Type) : Type :=
  list Alphabet -> Prop.

Definition q422187_language_equiv
    {Alphabet : Type}
    (L K : q422187_language Alphabet) : Prop :=
  forall word : list Alphabet, L word <-> K word.

Definition q422187_left_quotient
    {Alphabet : Type}
    (L : q422187_language Alphabet)
    (prefix : list Alphabet) : q422187_language Alphabet :=
  fun suffix => L (prefix ++ suffix).

Record q422187_finite_type (X : Type) : Type := {
  q422187_enumeration : list X;
  q422187_enumeration_complete :
    forall x : X, In x q422187_enumeration
}.

Record q422187_dfa (Alphabet State : Type) : Type := {
  q422187_step : State -> Alphabet -> State;
  q422187_start : State;
  q422187_accepting : State -> Prop
}.

Arguments q422187_step {Alphabet State} _ _ _.
Arguments q422187_start {Alphabet State} _.
Arguments q422187_accepting {Alphabet State} _ _.

Fixpoint q422187_eval_from
    {Alphabet State : Type}
    (M : q422187_dfa Alphabet State)
    (state : State)
    (word : list Alphabet) : State :=
  match word with
  | [] => state
  | symbol :: rest =>
      q422187_eval_from M (q422187_step M state symbol) rest
  end.

Definition q422187_accepts
    {Alphabet State : Type}
    (M : q422187_dfa Alphabet State) : q422187_language Alphabet :=
  fun word =>
    q422187_accepting M
      (q422187_eval_from M (q422187_start M) word).

Definition q422187_is_regular
    {Alphabet : Type}
    (L : q422187_language Alphabet) : Prop :=
  exists State : Type,
    exists _ : q422187_finite_type State,
      exists M : q422187_dfa Alphabet State,
        q422187_language_equiv (q422187_accepts M) L.

Definition q422187_left_quotient_range
    {Alphabet : Type}
    (L : q422187_language Alphabet)
    (quotient : q422187_language Alphabet) : Prop :=
  exists prefix : list Alphabet,
    q422187_language_equiv
      (q422187_left_quotient L prefix) quotient.

Definition q422187_finite_left_quotient_range
    {Alphabet : Type}
    (L : q422187_language Alphabet) : Prop :=
  exists quotients : list (q422187_language Alphabet),
    forall quotient : q422187_language Alphabet,
      q422187_left_quotient_range L quotient ->
      exists representative : q422187_language Alphabet,
        In representative quotients /\
        q422187_language_equiv quotient representative.

Theorem isRegular_iff_finite_range_leftQuotient :
  forall (Alphabet : Type) (L : q422187_language Alphabet),
    q422187_is_regular L <->
    q422187_finite_left_quotient_range L.
Admitted.

End Q422187_MyhillNerode.
