(*
  Statement-only formalization of Thousand Theorems corpus artifact Q208416
  (thousand-theorems__rocq__Q208416), "Independence of the continuum
  hypothesis": in a deep embedding of first-order ZFC, neither the continuum
  hypothesis sentence nor its negation is derivable. This file contains no
  proof.
*)

From Stdlib Require Import Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Inductive q208416_term (variables : nat) : Type :=
| q208416_var : Fin.t variables -> q208416_term variables
| q208416_empty : q208416_term variables
| q208416_pair :
    q208416_term variables ->
    q208416_term variables ->
    q208416_term variables
| q208416_omega : q208416_term variables
| q208416_powerset :
    q208416_term variables ->
    q208416_term variables
| q208416_union :
    q208416_term variables ->
    q208416_term variables.

Arguments q208416_var {variables} _.
Arguments q208416_empty {variables}.
Arguments q208416_pair {variables} _ _.
Arguments q208416_omega {variables}.
Arguments q208416_powerset {variables} _.
Arguments q208416_union {variables} _.

Inductive q208416_formula (variables : nat) : Type :=
| q208416_falsum : q208416_formula variables
| q208416_equal :
    q208416_term variables ->
    q208416_term variables ->
    q208416_formula variables
| q208416_member :
    q208416_term variables ->
    q208416_term variables ->
    q208416_formula variables
| q208416_implies :
    q208416_formula variables ->
    q208416_formula variables ->
    q208416_formula variables
| q208416_forall :
    q208416_formula (S variables) ->
    q208416_formula variables.

Arguments q208416_falsum {variables}.
Arguments q208416_equal {variables} _ _.
Arguments q208416_member {variables} _ _.
Arguments q208416_implies {variables} _ _.
Arguments q208416_forall {variables} _.

Fixpoint q208416_term_map
    {n m : nat}
    (rho : Fin.t n -> Fin.t m)
    (t : q208416_term n) : q208416_term m :=
  match t with
  | q208416_var i => q208416_var (rho i)
  | q208416_empty => q208416_empty
  | q208416_pair x y =>
      q208416_pair
        (q208416_term_map rho x)
        (q208416_term_map rho y)
  | q208416_omega => q208416_omega
  | q208416_powerset x =>
      q208416_powerset (q208416_term_map rho x)
  | q208416_union x =>
      q208416_union (q208416_term_map rho x)
  end.

Definition q208416_lift_substitution
    {n m : nat}
    (sigma : Fin.t n -> q208416_term m)
    (i : Fin.t (S n)) : q208416_term (S m) :=
  Fin.caseS' i
    (fun _ => q208416_term (S m))
    (q208416_var Fin.F1)
    (fun j =>
       q208416_term_map Fin.FS (sigma j)).

Fixpoint q208416_term_substitute
    {n m : nat}
    (sigma : Fin.t n -> q208416_term m)
    (t : q208416_term n) : q208416_term m :=
  match t with
  | q208416_var i => sigma i
  | q208416_empty => q208416_empty
  | q208416_pair x y =>
      q208416_pair
        (q208416_term_substitute sigma x)
        (q208416_term_substitute sigma y)
  | q208416_omega => q208416_omega
  | q208416_powerset x =>
      q208416_powerset (q208416_term_substitute sigma x)
  | q208416_union x =>
      q208416_union (q208416_term_substitute sigma x)
  end.

Fixpoint q208416_formula_substitute
    {n m : nat}
    (sigma : Fin.t n -> q208416_term m)
    (phi : q208416_formula n) : q208416_formula m :=
  match phi with
  | q208416_falsum => q208416_falsum
  | q208416_equal x y =>
      q208416_equal
        (q208416_term_substitute sigma x)
        (q208416_term_substitute sigma y)
  | q208416_member x y =>
      q208416_member
        (q208416_term_substitute sigma x)
        (q208416_term_substitute sigma y)
  | q208416_implies psi chi =>
      q208416_implies
        (q208416_formula_substitute sigma psi)
        (q208416_formula_substitute sigma chi)
  | q208416_forall psi =>
      q208416_forall
        (q208416_formula_substitute
           (q208416_lift_substitution sigma) psi)
  end.

Definition q208416_formula_map
    {n m : nat}
    (rho : Fin.t n -> Fin.t m)
    (phi : q208416_formula n) : q208416_formula m :=
  q208416_formula_substitute
    (fun i => q208416_var (rho i)) phi.

Definition q208416_weaken_term
    {n : nat}
    (t : q208416_term n) : q208416_term (S n) :=
  q208416_term_map Fin.FS t.

Definition q208416_weaken_formula
    {n : nat}
    (phi : q208416_formula n) : q208416_formula (S n) :=
  q208416_formula_map Fin.FS phi.

Definition q208416_substitute_zero_map
    {n : nat}
    (t : q208416_term n)
    (i : Fin.t (S n)) : q208416_term n :=
  Fin.caseS' i
    (fun _ => q208416_term n)
    t
    (fun j => q208416_var j).

Definition q208416_substitute_zero
    {n : nat}
    (phi : q208416_formula (S n))
    (t : q208416_term n) : q208416_formula n :=
  q208416_formula_substitute
    (q208416_substitute_zero_map t) phi.

Definition q208416_not
    {n : nat}
    (phi : q208416_formula n) : q208416_formula n :=
  q208416_implies phi q208416_falsum.

Definition q208416_and
    {n : nat}
    (phi psi : q208416_formula n) : q208416_formula n :=
  q208416_not (q208416_implies phi (q208416_not psi)).

Definition q208416_or
    {n : nat}
    (phi psi : q208416_formula n) : q208416_formula n :=
  q208416_implies (q208416_not phi) psi.

Definition q208416_iff
    {n : nat}
    (phi psi : q208416_formula n) : q208416_formula n :=
  q208416_and
    (q208416_implies phi psi)
    (q208416_implies psi phi).

Definition q208416_exists
    {n : nat}
    (phi : q208416_formula (S n)) : q208416_formula n :=
  q208416_not (q208416_forall (q208416_not phi)).

Definition q208416_v0 {n : nat} : q208416_term (S n) :=
  q208416_var Fin.F1.

Definition q208416_v1 {n : nat} : q208416_term (S (S n)) :=
  q208416_var (Fin.FS Fin.F1).

Definition q208416_v2 {n : nat} : q208416_term (S (S (S n))) :=
  q208416_var (Fin.FS (Fin.FS Fin.F1)).

Definition q208416_v3 {n : nat} :
    q208416_term (S (S (S (S n)))) :=
  q208416_var (Fin.FS (Fin.FS (Fin.FS Fin.F1))).

Definition q208416_shift1
    {n : nat}
    (i : Fin.t n) : q208416_term (S n) :=
  q208416_var (Fin.FS i).

Definition q208416_shift2
    {n : nat}
    (i : Fin.t n) : q208416_term (S (S n)) :=
  q208416_var (Fin.FS (Fin.FS i)).

Definition q208416_shift3
    {n : nat}
    (i : Fin.t n) : q208416_term (S (S (S n))) :=
  q208416_var (Fin.FS (Fin.FS (Fin.FS i))).

Definition q208416_shift4
    {n : nat}
    (i : Fin.t n) : q208416_term (S (S (S (S n)))) :=
  q208416_var (Fin.FS (Fin.FS (Fin.FS (Fin.FS i)))).

Definition q208416_subset
    {n : nat}
    (x y : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0
          (q208416_weaken_term x))
       (q208416_member q208416_v0
          (q208416_weaken_term y))).

Definition q208416_is_transitive
    {n : nat}
    (z : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0
          (q208416_weaken_term z))
       (q208416_subset q208416_v0
          (q208416_weaken_term z))).

Definition q208416_epsilon_trichotomy
    {n : nat}
    (z : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0
          (q208416_weaken_term z))
       (q208416_forall
          (q208416_implies
             (q208416_member q208416_v0
                (q208416_weaken_term
                   (q208416_weaken_term z)))
             (q208416_or
                (q208416_equal q208416_v1 q208416_v0)
                (q208416_or
                   (q208416_member q208416_v1 q208416_v0)
                   (q208416_member q208416_v0 q208416_v1)))))).

Definition q208416_epsilon_well_founded
    {n : nat}
    (z : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_subset q208416_v0
          (q208416_weaken_term z))
       (q208416_implies
          (q208416_not
             (q208416_equal q208416_v0 q208416_empty))
          (q208416_exists
             (q208416_and
                (q208416_member q208416_v0 q208416_v1)
                (q208416_forall
                   (q208416_implies
                      (q208416_member q208416_v0 q208416_v2)
                      (q208416_not
                         (q208416_member
                            q208416_v0 q208416_v1)))))))).

Definition q208416_is_ordinal
    {n : nat}
    (z : q208416_term n) : q208416_formula n :=
  q208416_and
    (q208416_and
       (q208416_epsilon_trichotomy z)
       (q208416_epsilon_well_founded z))
    (q208416_is_transitive z).

Definition q208416_is_limit
    {n : nat}
    (z : q208416_term n) : q208416_formula n :=
  q208416_and
    (q208416_member q208416_empty z)
    (q208416_forall
       (q208416_implies
          (q208416_member q208416_v0
             (q208416_weaken_term z))
          (q208416_exists
             (q208416_and
                (q208416_member q208416_v0
                   (q208416_weaken_term
                      (q208416_weaken_term z)))
                (q208416_member q208416_v1 q208416_v0))))).

Definition q208416_axiom_emptyset : q208416_formula 0 :=
  q208416_forall
    (q208416_not
       (q208416_member q208416_v0 q208416_empty)).

Definition q208416_axiom_ordered_pairs : q208416_formula 0 :=
  q208416_forall
    (q208416_forall
       (q208416_forall
          (q208416_forall
             (q208416_iff
                (q208416_equal
                   (q208416_pair q208416_v3 q208416_v2)
                   (q208416_pair q208416_v1 q208416_v0))
                (q208416_and
                   (q208416_equal q208416_v3 q208416_v1)
                   (q208416_equal q208416_v2 q208416_v0)))))).

Definition q208416_axiom_extensionality : q208416_formula 0 :=
  q208416_forall
    (q208416_forall
       (q208416_implies
          (q208416_forall
             (q208416_iff
                (q208416_member q208416_v0 q208416_v2)
                (q208416_member q208416_v0 q208416_v1)))
          (q208416_equal q208416_v1 q208416_v0))).

Definition q208416_axiom_union : q208416_formula 0 :=
  q208416_forall
    (q208416_forall
       (q208416_iff
          (q208416_member q208416_v0
             (q208416_union q208416_v1))
          (q208416_exists
             (q208416_and
                (q208416_member q208416_v0 q208416_v2)
                (q208416_member q208416_v1 q208416_v0))))).

Definition q208416_axiom_powerset : q208416_formula 0 :=
  q208416_forall
    (q208416_forall
       (q208416_iff
          (q208416_member q208416_v0
             (q208416_powerset q208416_v1))
          (q208416_forall
             (q208416_implies
                (q208416_member q208416_v0 q208416_v1)
                (q208416_member q208416_v0 q208416_v2))))).

Definition q208416_axiom_infinity : q208416_formula 0 :=
  q208416_and
    (q208416_is_limit q208416_omega)
    (q208416_and
       (q208416_exists
          (q208416_and
             (q208416_is_ordinal q208416_v0)
             (q208416_equal
                (q208416_weaken_term q208416_omega)
                q208416_v0)))
       (q208416_forall
          (q208416_implies
             (q208416_is_ordinal q208416_v0)
             (q208416_implies
                (q208416_is_limit q208416_v0)
                (q208416_subset
                   (q208416_weaken_term q208416_omega)
                   q208416_v0))))).

Definition q208416_axiom_regularity : q208416_formula 0 :=
  q208416_forall
    (q208416_implies
       (q208416_not
          (q208416_equal q208416_v0 q208416_empty))
       (q208416_exists
          (q208416_and
             (q208416_member q208416_v0 q208416_v1)
             (q208416_forall
                (q208416_implies
                   (q208416_member q208416_v0 q208416_v2)
                   (q208416_not
                      (q208416_member
                         q208416_v0 q208416_v1))))))).

Definition q208416_is_chain
    {n : nat}
    (y z : q208416_term n) : q208416_formula n :=
  q208416_and
    (q208416_subset y z)
    (q208416_forall
       (q208416_forall
          (q208416_implies
             (q208416_and
                (q208416_member q208416_v1
                   (q208416_weaken_term
                      (q208416_weaken_term y)))
                (q208416_member q208416_v0
                   (q208416_weaken_term
                      (q208416_weaken_term y))))
             (q208416_or
                (q208416_subset q208416_v1 q208416_v0)
                (q208416_subset q208416_v0 q208416_v1))))).

Definition q208416_zorns_lemma : q208416_formula 0 :=
  q208416_forall
    (q208416_implies
       (q208416_not
          (q208416_equal q208416_v0 q208416_empty))
       (q208416_implies
          (q208416_forall
             (q208416_implies
                (q208416_is_chain q208416_v0 q208416_v1)
                (q208416_member
                   (q208416_union q208416_v0)
                   q208416_v1)))
          (q208416_exists
             (q208416_and
                (q208416_member q208416_v0 q208416_v1)
                (q208416_forall
                   (q208416_implies
                      (q208416_member q208416_v0 q208416_v2)
                      (q208416_implies
                         (q208416_subset
                            q208416_v1 q208416_v0)
                         (q208416_equal
                            q208416_v1 q208416_v0)))))))).

Definition q208416_instantiate2
    {n m : nat}
    (phi : q208416_formula (S (S n)))
    (y x : q208416_term m)
    (parameters : Fin.t n -> q208416_term m) :
    q208416_formula m :=
  q208416_formula_substitute
    (fun i =>
       Fin.caseS' i
         (fun _ => q208416_term m)
         y
         (fun j =>
            Fin.caseS' j
              (fun _ => q208416_term m)
              x
              parameters)) phi.

Definition q208416_collection_antecedent
    {n : nat}
    (phi : q208416_formula (S (S n))) :
    q208416_formula (S n) :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0 q208416_v1)
       (q208416_exists
          (q208416_instantiate2
             phi q208416_v0 q208416_v1
             q208416_shift3))).

Definition q208416_collection_forward
    {n : nat}
    (phi : q208416_formula (S (S n))) :
    q208416_formula (S (S n)) :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0 q208416_v2)
       (q208416_exists
          (q208416_and
             (q208416_member q208416_v0 q208416_v2)
             (q208416_instantiate2
                phi q208416_v0 q208416_v1
                q208416_shift4)))).

Definition q208416_collection_backward
    {n : nat}
    (phi : q208416_formula (S (S n))) :
    q208416_formula (S (S n)) :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0 q208416_v1)
       (q208416_exists
          (q208416_and
             (q208416_member q208416_v0 q208416_v3)
             (q208416_instantiate2
                phi q208416_v1 q208416_v0
                q208416_shift4)))).

Fixpoint q208416_close_all
    (n : nat) : q208416_formula n -> q208416_formula 0 :=
  match n as k return q208416_formula k -> q208416_formula 0 with
  | 0 => fun phi => phi
  | S k =>
      fun phi => @q208416_close_all k (q208416_forall phi)
  end.

Definition q208416_axiom_collection
    {n : nat}
    (phi : q208416_formula (S (S n))) : q208416_formula 0 :=
  @q208416_close_all n
    (q208416_forall
       (q208416_implies
          (q208416_collection_antecedent phi)
          (q208416_exists
             (q208416_and
                (q208416_collection_forward phi)
                (q208416_collection_backward phi))))).

Definition q208416_ZFC
    (sentence : q208416_formula 0) : Prop :=
  sentence = q208416_axiom_emptyset \/
  sentence = q208416_axiom_ordered_pairs \/
  sentence = q208416_axiom_extensionality \/
  sentence = q208416_axiom_union \/
  sentence = q208416_axiom_powerset \/
  sentence = q208416_axiom_infinity \/
  sentence = q208416_axiom_regularity \/
  sentence = q208416_zorns_lemma \/
  exists (n : nat) (phi : q208416_formula (S (S n))),
    sentence = q208416_axiom_collection phi.

Definition q208416_is_functional
    {n : nat}
    (f : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_forall
       (q208416_forall
          (q208416_forall
             (q208416_implies
                (q208416_and
                   (q208416_member
                      (q208416_pair q208416_v3 q208416_v1)
                      (q208416_term_substitute q208416_shift4 f))
                   (q208416_member
                      (q208416_pair q208416_v2 q208416_v0)
                      (q208416_term_substitute q208416_shift4 f)))
                (q208416_implies
                   (q208416_equal q208416_v3 q208416_v2)
                   (q208416_equal q208416_v1 q208416_v0)))))).

Definition q208416_is_total
    {n : nat}
    (f domain codomain : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0
          (q208416_weaken_term domain))
       (q208416_exists
          (q208416_and
             (q208416_member q208416_v0
                (q208416_term_substitute q208416_shift2 codomain))
             (q208416_member
                (q208416_pair q208416_v1 q208416_v0)
                (q208416_term_substitute q208416_shift2 f))))).

Definition q208416_is_surjective
    {n : nat}
    (f domain codomain : q208416_term n) : q208416_formula n :=
  q208416_forall
    (q208416_implies
       (q208416_member q208416_v0
          (q208416_weaken_term codomain))
       (q208416_exists
          (q208416_and
             (q208416_member q208416_v0
                (q208416_term_substitute q208416_shift2 domain))
             (q208416_member
                (q208416_pair q208416_v0 q208416_v1)
                (q208416_term_substitute q208416_shift2 f))))).

Definition q208416_is_function_from_to
    {n : nat}
    (f domain codomain : q208416_term n) : q208416_formula n :=
  q208416_and
    (q208416_is_functional f)
    (q208416_is_total f domain codomain).

Definition q208416_at_most
    {n : nat}
    (x y : q208416_term n) : q208416_formula n :=
  q208416_exists
    (q208416_exists
       (q208416_and
          (q208416_and
             (q208416_subset q208416_v1
                (q208416_term_substitute q208416_shift2 y))
             (q208416_is_function_from_to
                q208416_v0 q208416_v1
                (q208416_term_substitute q208416_shift2 x)))
          (q208416_is_surjective
             q208416_v0 q208416_v1
             (q208416_term_substitute q208416_shift2 x)))).

Definition q208416_CH : q208416_formula 0 :=
  q208416_forall
    (q208416_implies
       (q208416_is_ordinal q208416_v0)
       (q208416_or
          (q208416_at_most
             q208416_v0 q208416_omega)
          (q208416_at_most
             (q208416_powerset q208416_omega)
             q208416_v0))).

Unset Implicit Arguments.

Inductive q208416_derivation :
    forall n : nat,
      (q208416_formula n -> Prop) ->
      q208416_formula n ->
      Type :=
| q208416_prf_axiom :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A : q208416_formula n),
      Gamma A ->
      q208416_derivation n Gamma A
| q208416_prf_implies_intro :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A B : q208416_formula n),
      q208416_derivation n
        (fun C => C = A \/ Gamma C) B ->
      q208416_derivation n Gamma
        (q208416_implies A B)
| q208416_prf_implies_elim :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A B : q208416_formula n),
      q208416_derivation n Gamma
        (q208416_implies A B) ->
      q208416_derivation n Gamma A ->
      q208416_derivation n Gamma B
| q208416_prf_classical_absurd :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A : q208416_formula n),
      q208416_derivation n
        (fun C => C = q208416_not A \/ Gamma C)
        q208416_falsum ->
      q208416_derivation n Gamma A
| q208416_prf_forall_intro :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A : q208416_formula (S n)),
      q208416_derivation (S n)
        (fun B =>
           exists C : q208416_formula n,
             Gamma C /\ B = q208416_weaken_formula C)
        A ->
      q208416_derivation n Gamma
        (q208416_forall A)
| q208416_prf_forall_elim :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (A : q208416_formula (S n))
      (t : q208416_term n),
      q208416_derivation n Gamma
        (q208416_forall A) ->
      q208416_derivation n Gamma
        (q208416_substitute_zero A t)
| q208416_prf_reflexivity :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (t : q208416_term n),
      q208416_derivation n Gamma
        (q208416_equal t t)
| q208416_prf_equality_substitution :
    forall (n : nat)
      (Gamma : q208416_formula n -> Prop)
      (s t : q208416_term n)
      (phi : q208416_formula (S n)),
      q208416_derivation n Gamma
        (q208416_equal s t) ->
      q208416_derivation n Gamma
        (q208416_substitute_zero phi s) ->
      q208416_derivation n Gamma
        (q208416_substitute_zero phi t).

Definition q208416_provable
    (T : q208416_formula 0 -> Prop)
    (phi : q208416_formula 0) : Prop :=
  inhabited (q208416_derivation 0 T phi).

Definition q208416_independent
    (T : q208416_formula 0 -> Prop)
    (phi : q208416_formula 0) : Prop :=
  ~ q208416_provable T phi /\
  ~ q208416_provable T (q208416_not phi).

Theorem independence_of_CH :
  q208416_independent q208416_ZFC q208416_CH.
Admitted.
