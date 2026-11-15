(*
  Statement-only formalization of Thousand Theorems corpus artifact Q20971632
  (thousand-theorems__rocq__Q20971632), "Lie's theorem": a finite-dimensional
  triangularizable module over a solvable Lie algebra in characteristic zero
  has a nonzero common eigenvector. This file contains no proof.
*)

From Stdlib Require Import Lists.List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q20971632_field (K : Type) : Type := {
  q20971632_zero : K;
  q20971632_one : K;
  q20971632_add : K -> K -> K;
  q20971632_mul : K -> K -> K;
  q20971632_neg : K -> K;
  q20971632_inv : K -> K;
  q20971632_add_assoc :
    forall x y z : K,
      q20971632_add x (q20971632_add y z) =
      q20971632_add (q20971632_add x y) z;
  q20971632_add_comm :
    forall x y : K,
      q20971632_add x y = q20971632_add y x;
  q20971632_zero_add :
    forall x : K, q20971632_add q20971632_zero x = x;
  q20971632_add_zero :
    forall x : K, q20971632_add x q20971632_zero = x;
  q20971632_neg_add :
    forall x : K,
      q20971632_add (q20971632_neg x) x = q20971632_zero;
  q20971632_add_neg :
    forall x : K,
      q20971632_add x (q20971632_neg x) = q20971632_zero;
  q20971632_mul_assoc :
    forall x y z : K,
      q20971632_mul x (q20971632_mul y z) =
      q20971632_mul (q20971632_mul x y) z;
  q20971632_mul_comm :
    forall x y : K,
      q20971632_mul x y = q20971632_mul y x;
  q20971632_one_mul :
    forall x : K, q20971632_mul q20971632_one x = x;
  q20971632_mul_one :
    forall x : K, q20971632_mul x q20971632_one = x;
  q20971632_mul_add :
    forall x y z : K,
      q20971632_mul x (q20971632_add y z) =
      q20971632_add
        (q20971632_mul x y) (q20971632_mul x z);
  q20971632_add_mul :
    forall x y z : K,
      q20971632_mul (q20971632_add x y) z =
      q20971632_add
        (q20971632_mul x z) (q20971632_mul y z);
  q20971632_zero_ne_one :
    q20971632_zero <> q20971632_one;
  q20971632_mul_inv :
    forall x : K,
      x <> q20971632_zero ->
      q20971632_mul x (q20971632_inv x) = q20971632_one
}.

Arguments q20971632_zero {K} _.
Arguments q20971632_one {K} _.
Arguments q20971632_add {K} _ _ _.
Arguments q20971632_mul {K} _ _ _.
Arguments q20971632_neg {K} _ _.
Arguments q20971632_inv {K} _ _.

Fixpoint q20971632_nat_cast
    {K : Type} (F : q20971632_field K) (n : nat) : K :=
  match n with
  | O => q20971632_zero F
  | S m =>
      q20971632_add F
        (q20971632_one F) (q20971632_nat_cast F m)
  end.

Definition q20971632_char_zero
    {K : Type} (F : q20971632_field K) : Prop :=
  forall n m : nat,
    q20971632_nat_cast F n = q20971632_nat_cast F m ->
    n = m.

Record q20971632_vector_space
    {K : Type} (F : q20971632_field K) (X : Type) : Type := {
  q20971632_vzero : X;
  q20971632_vadd : X -> X -> X;
  q20971632_vneg : X -> X;
  q20971632_smul : K -> X -> X;
  q20971632_vadd_assoc :
    forall x y z : X,
      q20971632_vadd x (q20971632_vadd y z) =
      q20971632_vadd (q20971632_vadd x y) z;
  q20971632_vadd_comm :
    forall x y : X, q20971632_vadd x y = q20971632_vadd y x;
  q20971632_vzero_add :
    forall x : X, q20971632_vadd q20971632_vzero x = x;
  q20971632_vadd_zero :
    forall x : X, q20971632_vadd x q20971632_vzero = x;
  q20971632_vneg_add :
    forall x : X,
      q20971632_vadd (q20971632_vneg x) x = q20971632_vzero;
  q20971632_vadd_neg :
    forall x : X,
      q20971632_vadd x (q20971632_vneg x) = q20971632_vzero;
  q20971632_one_smul :
    forall x : X, q20971632_smul (q20971632_one F) x = x;
  q20971632_mul_smul :
    forall (a b : K) (x : X),
      q20971632_smul (q20971632_mul F a b) x =
      q20971632_smul a (q20971632_smul b x);
  q20971632_add_smul :
    forall (a b : K) (x : X),
      q20971632_smul (q20971632_add F a b) x =
      q20971632_vadd
        (q20971632_smul a x) (q20971632_smul b x);
  q20971632_smul_add :
    forall (a : K) (x y : X),
      q20971632_smul a (q20971632_vadd x y) =
      q20971632_vadd
        (q20971632_smul a x) (q20971632_smul a y);
  q20971632_zero_smul :
    forall x : X,
      q20971632_smul (q20971632_zero F) x = q20971632_vzero;
  q20971632_smul_zero :
    forall a : K, q20971632_smul a q20971632_vzero = q20971632_vzero
}.

Arguments q20971632_vzero {K F X} _.
Arguments q20971632_vadd {K F X} _ _ _.
Arguments q20971632_vneg {K F X} _ _.
Arguments q20971632_smul {K F X} _ _ _.

Record q20971632_lie_algebra
    {K : Type}
    {F : q20971632_field K}
    {L : Type}
    (LS : q20971632_vector_space F L) : Type := {
  q20971632_bracket : L -> L -> L;
  q20971632_bracket_add_left :
    forall x y z : L,
      q20971632_bracket (q20971632_vadd LS x y) z =
      q20971632_vadd LS
        (q20971632_bracket x z) (q20971632_bracket y z);
  q20971632_bracket_add_right :
    forall x y z : L,
      q20971632_bracket x (q20971632_vadd LS y z) =
      q20971632_vadd LS
        (q20971632_bracket x y) (q20971632_bracket x z);
  q20971632_bracket_smul_left :
    forall (a : K) (x y : L),
      q20971632_bracket (q20971632_smul LS a x) y =
      q20971632_smul LS a (q20971632_bracket x y);
  q20971632_bracket_smul_right :
    forall (a : K) (x y : L),
      q20971632_bracket x (q20971632_smul LS a y) =
      q20971632_smul LS a (q20971632_bracket x y);
  q20971632_bracket_self :
    forall x : L,
      q20971632_bracket x x = q20971632_vzero LS;
  q20971632_jacobi :
    forall x y z : L,
      q20971632_vadd LS
        (q20971632_bracket x (q20971632_bracket y z))
        (q20971632_vadd LS
          (q20971632_bracket y (q20971632_bracket z x))
          (q20971632_bracket z (q20971632_bracket x y))) =
      q20971632_vzero LS
}.

Arguments q20971632_bracket {K F L LS} _ _ _.

Record q20971632_lie_module
    {K : Type}
    {F : q20971632_field K}
    {L V : Type}
    (LS : q20971632_vector_space F L)
    (LA : q20971632_lie_algebra LS)
    (VS : q20971632_vector_space F V) : Type := {
  q20971632_action : L -> V -> V;
  q20971632_action_add_left :
    forall x y : L, forall v : V,
      q20971632_action (q20971632_vadd LS x y) v =
      q20971632_vadd VS
        (q20971632_action x v) (q20971632_action y v);
  q20971632_action_add_right :
    forall x : L, forall v w : V,
      q20971632_action x (q20971632_vadd VS v w) =
      q20971632_vadd VS
        (q20971632_action x v) (q20971632_action x w);
  q20971632_action_smul_left :
    forall (a : K) (x : L) (v : V),
      q20971632_action (q20971632_smul LS a x) v =
      q20971632_smul VS a (q20971632_action x v);
  q20971632_action_smul_right :
    forall (a : K) (x : L) (v : V),
      q20971632_action x (q20971632_smul VS a v) =
      q20971632_smul VS a (q20971632_action x v);
  q20971632_action_bracket :
    forall (x y : L) (v : V),
      q20971632_action (q20971632_bracket LA x y) v =
      q20971632_vadd VS
        (q20971632_action x (q20971632_action y v))
        (q20971632_vneg VS
          (q20971632_action y (q20971632_action x v)))
}.

Arguments q20971632_action {K F L V LS LA VS} _ _ _.

Fixpoint q20971632_linear_combination
    {K : Type}
    {F : q20971632_field K}
    {X : Type}
    (XS : q20971632_vector_space F X)
    (terms : list (K * X)) : X :=
  match terms with
  | [] => q20971632_vzero XS
  | (a, x) :: rest =>
      q20971632_vadd XS
        (q20971632_smul XS a x)
        (q20971632_linear_combination XS rest)
  end.

Definition q20971632_finite_dimensional
    {K : Type}
    {F : q20971632_field K}
    {X : Type}
    (XS : q20971632_vector_space F X) : Prop :=
  exists generators : list X,
    forall x : X,
      exists terms : list (K * X),
        Forall (fun term => In (snd term) generators) terms /\
        x = q20971632_linear_combination XS terms.

Definition q20971632_nontrivial
    {K : Type}
    {F : q20971632_field K}
    {X : Type}
    (XS : q20971632_vector_space F X) : Prop :=
  exists x : X, x <> q20971632_vzero XS.

Definition q20971632_linear_span
    {K : Type}
    {F : q20971632_field K}
    {X : Type}
    (XS : q20971632_vector_space F X)
    (S : X -> Prop)
    (x : X) : Prop :=
  forall P : X -> Prop,
    P (q20971632_vzero XS) ->
    (forall u v : X,
      P u -> P v -> P (q20971632_vadd XS u v)) ->
    (forall u : X,
      P u -> P (q20971632_vneg XS u)) ->
    (forall (a : K) (u : X),
      P u -> P (q20971632_smul XS a u)) ->
    (forall u : X, S u -> P u) ->
    P x.

Fixpoint q20971632_derived_series
    {K : Type}
    {F : q20971632_field K}
    {L : Type}
    (LS : q20971632_vector_space F L)
    (LA : q20971632_lie_algebra LS)
    (n : nat) : L -> Prop :=
  match n with
  | O => fun _ => True
  | S m =>
      fun z =>
        q20971632_linear_span LS
          (fun b =>
            exists x y : L,
              @q20971632_derived_series K F L LS LA m x /\
              @q20971632_derived_series K F L LS LA m y /\
              b = q20971632_bracket LA x y)
          z
  end.

Definition q20971632_is_solvable
    {K : Type}
    {F : q20971632_field K}
    {L : Type}
    (LS : q20971632_vector_space F L)
    (LA : q20971632_lie_algebra LS) : Prop :=
  exists n : nat,
    forall x : L,
      @q20971632_derived_series K F L LS LA n x ->
      x = q20971632_vzero LS.

Definition q20971632_deviation
    {K : Type}
    {F : q20971632_field K}
    {L V : Type}
    {LS : q20971632_vector_space F L}
    {LA : q20971632_lie_algebra LS}
    {VS : q20971632_vector_space F V}
    (M : @q20971632_lie_module K F L V LS LA VS)
    (x : L) (lambda : K) (v : V) : V :=
  q20971632_vadd VS
    (q20971632_action M x v)
    (q20971632_vneg VS (q20971632_smul VS lambda v)).

Fixpoint q20971632_iterated_deviation
    {K : Type}
    {F : q20971632_field K}
    {L V : Type}
    {LS : q20971632_vector_space F L}
    {LA : q20971632_lie_algebra LS}
    {VS : q20971632_vector_space F V}
    (M : @q20971632_lie_module K F L V LS LA VS)
    (x : L) (lambda : K) (n : nat) (v : V) : V :=
  match n with
  | O => v
  | S m =>
      q20971632_deviation M x lambda
        (q20971632_iterated_deviation M x lambda m v)
  end.

Definition q20971632_generalized_eigenvector
    {K : Type}
    {F : q20971632_field K}
    {L V : Type}
    {LS : q20971632_vector_space F L}
    {LA : q20971632_lie_algebra LS}
    {VS : q20971632_vector_space F V}
    (M : @q20971632_lie_module K F L V LS LA VS)
    (x : L) (lambda : K) (v : V) : Prop :=
  exists n : nat,
    q20971632_iterated_deviation M x lambda n v =
    q20971632_vzero VS.

Fixpoint q20971632_sum_generalized_vectors
    {K : Type}
    {F : q20971632_field K}
    {V : Type}
    (VS : q20971632_vector_space F V)
    (terms : list (K * V)) : V :=
  match terms with
  | [] => q20971632_vzero VS
  | (_, v) :: rest =>
      q20971632_vadd VS v
        (q20971632_sum_generalized_vectors VS rest)
  end.

Definition q20971632_is_triangularizable
    {K : Type}
    {F : q20971632_field K}
    {L V : Type}
    {LS : q20971632_vector_space F L}
    {LA : q20971632_lie_algebra LS}
    {VS : q20971632_vector_space F V}
    (M : @q20971632_lie_module K F L V LS LA VS) : Prop :=
  forall (x : L) (v : V),
    exists terms : list (K * V),
      v = q20971632_sum_generalized_vectors VS terms /\
      Forall
        (fun term =>
          q20971632_generalized_eigenvector
            M x (fst term) (snd term))
        terms.

Record q20971632_linear_functional
    {K : Type}
    {F : q20971632_field K}
    {L : Type}
    (LS : q20971632_vector_space F L) : Type := {
  q20971632_functional_apply : L -> K;
  q20971632_functional_add :
    forall x y : L,
      q20971632_functional_apply (q20971632_vadd LS x y) =
      q20971632_add F
        (q20971632_functional_apply x)
        (q20971632_functional_apply y);
  q20971632_functional_smul :
    forall (a : K) (x : L),
      q20971632_functional_apply (q20971632_smul LS a x) =
      q20971632_mul F a (q20971632_functional_apply x)
}.

Arguments q20971632_functional_apply {K F L LS} _ _.

Theorem q20971632_lies_theorem :
  forall
    (K : Type)
    (F : q20971632_field K)
    (L : Type)
    (LS : q20971632_vector_space F L)
    (LA : q20971632_lie_algebra LS)
    (V : Type)
    (VS : q20971632_vector_space F V)
    (M : @q20971632_lie_module K F L V LS LA VS),
    q20971632_char_zero F ->
    q20971632_finite_dimensional VS ->
    q20971632_nontrivial VS ->
    @q20971632_is_solvable K F L LS LA ->
    q20971632_is_triangularizable M ->
    exists chi : q20971632_linear_functional LS,
      exists v : V,
        v <> q20971632_vzero VS /\
        forall x : L,
          q20971632_action M x v =
          q20971632_smul VS
            (q20971632_functional_apply chi x) v.
Admitted.
