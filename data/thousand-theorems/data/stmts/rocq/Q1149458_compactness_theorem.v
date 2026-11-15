(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1149458
  (thousand-theorems__rocq__Q1149458), "Compactness theorem": an arbitrary
  first-order theory has a nonempty model if and only if each of its finite
  subtheories has a nonempty model. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Polymorphic Record q1149458_language@{u v} : Type := {
  q1149458_functions : nat -> Type@{u};
  q1149458_relations : nat -> Type@{v}
}.

Polymorphic Inductive q1149458_list@{w}
    (A : Type@{w}) : Type@{w} :=
| q1149458_list_nil : q1149458_list A
| q1149458_list_cons : A -> q1149458_list A -> q1149458_list A.

Arguments q1149458_list_nil {A}.
Arguments q1149458_list_cons {A} _ _.

Polymorphic Fixpoint q1149458_member@{w}
    {A : Type@{w}} (x : A) (xs : q1149458_list@{w} A) : Prop :=
  match xs with
  | q1149458_list_nil => False
  | q1149458_list_cons y ys =>
      x = y \/ q1149458_member x ys
  end.

Polymorphic Inductive q1149458_tuple@{w}
    (A : Type@{w}) : nat -> Type@{w} :=
| q1149458_tuple_nil : q1149458_tuple A 0
| q1149458_tuple_cons :
    forall n, A -> q1149458_tuple A n -> q1149458_tuple A (S n).

Arguments q1149458_tuple_nil {A}.
Arguments q1149458_tuple_cons {A n} _ _.

Polymorphic Record q1149458_structure@{u v w
    | Set < w, u <= w, v <= w}
    (L : q1149458_language@{u v}) (A : Type@{w}) : Type@{w} := {
  q1149458_function_interpretation :
    forall n,
      q1149458_functions L n ->
      q1149458_tuple@{w} A n ->
      A;
  q1149458_relation_interpretation :
    forall n,
      q1149458_relations L n ->
      q1149458_tuple@{w} A n ->
      Prop
}.

Arguments q1149458_function_interpretation {L A} _ {n} _ _.
Arguments q1149458_relation_interpretation {L A} _ {n} _ _.

Polymorphic Inductive q1149458_term@{u v w
    | Set < w, u <= w, v <= w}
    (L : q1149458_language@{u v}) (variables : nat) : Type@{w} :=
| q1149458_variable :
    Fin.t variables ->
    q1149458_term L variables
| q1149458_function :
    forall arity,
      q1149458_functions L arity ->
      q1149458_terms L variables arity ->
      q1149458_term L variables
with q1149458_terms
    (L : q1149458_language@{u v})
    (variables : nat) : nat -> Type@{w} :=
| q1149458_terms_nil :
    q1149458_terms L variables 0
| q1149458_terms_cons :
    forall arity,
      q1149458_term L variables ->
      q1149458_terms L variables arity ->
      q1149458_terms L variables (S arity).

Arguments q1149458_variable {L variables} _.
Arguments q1149458_function {L variables arity} _ _.
Arguments q1149458_terms_nil {L variables}.
Arguments q1149458_terms_cons {L variables arity} _ _.

Polymorphic Fixpoint q1149458_term_denote@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    {A : Type@{w}}
    {variables : nat}
    (S : q1149458_structure@{u v w} L A)
    (valuation : Fin.t variables -> A)
    (t : q1149458_term@{u v w} L variables) : A :=
  match t with
  | q1149458_variable index => valuation index
  | q1149458_function function_symbol arguments =>
      q1149458_function_interpretation S function_symbol
        (q1149458_terms_denote S valuation arguments)
  end
with q1149458_terms_denote
    {L : q1149458_language@{u v}}
    {A : Type@{w}}
    {variables arity : nat}
    (S : q1149458_structure@{u v w} L A)
    (valuation : Fin.t variables -> A)
    (ts : q1149458_terms@{u v w} L variables arity) :
      q1149458_tuple@{w} A arity :=
  match ts with
  | q1149458_terms_nil => q1149458_tuple_nil
  | q1149458_terms_cons t rest =>
      q1149458_tuple_cons
        (q1149458_term_denote S valuation t)
        (q1149458_terms_denote S valuation rest)
  end.

Polymorphic Inductive q1149458_formula@{u v w
    | Set < w, u <= w, v <= w}
    (L : q1149458_language@{u v}) : nat -> Type@{w} :=
| q1149458_equal :
    forall variables,
      q1149458_term@{u v w} L variables ->
      q1149458_term@{u v w} L variables ->
      q1149458_formula L variables
| q1149458_atomic :
    forall variables arity,
      q1149458_relations L arity ->
      q1149458_terms@{u v w} L variables arity ->
      q1149458_formula L variables
| q1149458_falsum :
    forall variables, q1149458_formula L variables
| q1149458_implies :
    forall variables,
      q1149458_formula L variables ->
      q1149458_formula L variables ->
      q1149458_formula L variables
| q1149458_forall :
    forall variables,
      q1149458_formula L (S variables) ->
      q1149458_formula L variables.

Arguments q1149458_equal {L variables} _ _.
Arguments q1149458_atomic {L variables arity} _ _.
Arguments q1149458_falsum {L variables}.
Arguments q1149458_implies {L variables} _ _.
Arguments q1149458_forall {L variables} _.

Polymorphic Definition q1149458_extend_valuation@{w | Set < w}
    {A : Type@{w}}
    {variables : nat}
    (x : A)
    (valuation : Fin.t variables -> A)
    (index : Fin.t (S variables)) : A :=
  (match index in Fin.t size return
     match size with
     | 0 => A
     | S predecessor => (Fin.t predecessor -> A) -> A
     end
   with
   | @Fin.F1 _ => fun _ => x
   | @Fin.FS _ index' => fun predecessor_valuation =>
       predecessor_valuation index'
   end) valuation.

Polymorphic Fixpoint q1149458_satisfies@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    {A : Type@{w}}
    {variables : nat}
    (S : q1149458_structure@{u v w} L A)
    (valuation : Fin.t variables -> A)
    (phi : q1149458_formula@{u v w} L variables) : Prop :=
  (match phi in q1149458_formula _ matched_variables
     return (Fin.t matched_variables -> A) -> Prop with
  | q1149458_equal t u =>
      fun matched_valuation =>
        q1149458_term_denote S matched_valuation t =
        q1149458_term_denote S matched_valuation u
  | q1149458_atomic relation_symbol arguments =>
      fun matched_valuation =>
        q1149458_relation_interpretation S relation_symbol
          (q1149458_terms_denote S matched_valuation arguments)
  | q1149458_falsum => fun _ => False
  | q1149458_implies psi chi =>
      fun matched_valuation =>
        q1149458_satisfies S matched_valuation psi ->
        q1149458_satisfies S matched_valuation chi
  | q1149458_forall psi =>
      fun matched_valuation =>
        forall x : A,
          q1149458_satisfies S
            (q1149458_extend_valuation@{w} x matched_valuation) psi
  end) valuation.

Polymorphic Definition q1149458_sentence@{u v w
    | Set < w, u <= w, v <= w}
    (L : q1149458_language@{u v}) : Type@{w} :=
  q1149458_formula@{u v w} L 0.

Polymorphic Definition q1149458_theory@{u v w
    | Set < w, u <= w, v <= w}
    (L : q1149458_language@{u v}) : Type@{w} :=
  q1149458_sentence@{u v w} L -> Prop.

Polymorphic Definition q1149458_empty_valuation@{w | Set < w}
    {A : Type@{w}} (index : Fin.t 0) : A :=
  match index with
  end.

Polymorphic Definition q1149458_models@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    {A : Type@{w}}
    (S : q1149458_structure@{u v w} L A)
    (T : q1149458_theory@{u v w} L) : Prop :=
  forall phi : q1149458_sentence@{u v w} L,
    T phi ->
    q1149458_satisfies S q1149458_empty_valuation@{w} phi.

Polymorphic Definition q1149458_nonempty@{w}
    (A : Type@{w}) : Prop :=
  exists x : A, True.

Polymorphic Definition q1149458_is_satisfiable@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    (T : q1149458_theory@{u v w} L) : Prop :=
  exists (A : Type@{w})
      (S : q1149458_structure@{u v w} L A),
    q1149458_nonempty@{w} A /\
    q1149458_models@{u v w} S T.

Polymorphic Definition q1149458_list_theory@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    (sentences :
      q1149458_list@{w} (q1149458_sentence@{u v w} L)) :
      q1149458_theory@{u v w} L :=
  fun phi => q1149458_member@{w} phi sentences.

Polymorphic Definition q1149458_is_finitely_satisfiable@{u v w
    | Set < w, u <= w, v <= w}
    {L : q1149458_language@{u v}}
    (T : q1149458_theory@{u v w} L) : Prop :=
  forall sentences :
      q1149458_list@{w} (q1149458_sentence@{u v w} L),
    (forall phi : q1149458_sentence@{u v w} L,
      q1149458_member@{w} phi sentences -> T phi) ->
    @q1149458_is_satisfiable@{u v w}
      L (q1149458_list_theory@{u v w} sentences).

Polymorphic Theorem q1149458_compactness_theorem@{u v w
    | Set < w, u <= w, v <= w} :
  forall (L : q1149458_language@{u v})
      (T : q1149458_theory@{u v w} L),
    @q1149458_is_satisfiable@{u v w} L T <->
    @q1149458_is_finitely_satisfiable@{u v w} L T.
Admitted.
