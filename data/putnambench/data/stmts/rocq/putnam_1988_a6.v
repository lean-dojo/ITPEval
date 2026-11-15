(* Statement-only formalization of PutnamBench corpus artifact putnam_1988_a6:
   a linear operator on an n-dimensional vector space with n+1 eigenvectors,
   every n of which are linearly independent, is a scalar multiple of the
   identity. This file contains no proof. *)

From Stdlib Require Import Arith List.

Record putnam_1988_a6_field : Type := {
  p88_field_carrier : Type;
  p88_field_zero : p88_field_carrier;
  p88_field_one : p88_field_carrier;
  p88_field_add :
    p88_field_carrier -> p88_field_carrier -> p88_field_carrier;
  p88_field_mul :
    p88_field_carrier -> p88_field_carrier -> p88_field_carrier;
  p88_field_opp : p88_field_carrier -> p88_field_carrier;
  p88_field_inv : p88_field_carrier -> p88_field_carrier;
  p88_field_add_assoc :
    forall x y z,
      p88_field_add x (p88_field_add y z) =
      p88_field_add (p88_field_add x y) z;
  p88_field_add_comm :
    forall x y, p88_field_add x y = p88_field_add y x;
  p88_field_add_zero :
    forall x, p88_field_add p88_field_zero x = x;
  p88_field_add_opp :
    forall x, p88_field_add (p88_field_opp x) x = p88_field_zero;
  p88_field_mul_assoc :
    forall x y z,
      p88_field_mul x (p88_field_mul y z) =
      p88_field_mul (p88_field_mul x y) z;
  p88_field_mul_comm :
    forall x y, p88_field_mul x y = p88_field_mul y x;
  p88_field_mul_one :
    forall x, p88_field_mul p88_field_one x = x;
  p88_field_mul_add :
    forall x y z,
      p88_field_mul x (p88_field_add y z) =
      p88_field_add (p88_field_mul x y) (p88_field_mul x z);
  p88_field_zero_neq_one : p88_field_zero <> p88_field_one;
  p88_field_mul_inv :
    forall x,
      x <> p88_field_zero ->
      p88_field_mul (p88_field_inv x) x = p88_field_one
}.

Record putnam_1988_a6_vector_space
    (F : putnam_1988_a6_field) : Type := {
  p88_vector_carrier : Type;
  p88_vector_zero : p88_vector_carrier;
  p88_vector_add :
    p88_vector_carrier -> p88_vector_carrier -> p88_vector_carrier;
  p88_vector_opp : p88_vector_carrier -> p88_vector_carrier;
  p88_vector_scale :
    p88_field_carrier F ->
    p88_vector_carrier ->
    p88_vector_carrier;
  p88_vector_add_assoc :
    forall x y z,
      p88_vector_add x (p88_vector_add y z) =
      p88_vector_add (p88_vector_add x y) z;
  p88_vector_add_comm :
    forall x y, p88_vector_add x y = p88_vector_add y x;
  p88_vector_add_zero :
    forall x, p88_vector_add p88_vector_zero x = x;
  p88_vector_add_opp :
    forall x, p88_vector_add (p88_vector_opp x) x = p88_vector_zero;
  p88_scale_vector_add :
    forall a x y,
      p88_vector_scale a (p88_vector_add x y) =
      p88_vector_add (p88_vector_scale a x) (p88_vector_scale a y);
  p88_scale_field_add :
    forall a b x,
      p88_vector_scale (p88_field_add F a b) x =
      p88_vector_add (p88_vector_scale a x) (p88_vector_scale b x);
  p88_scale_assoc :
    forall a b x,
      p88_vector_scale a (p88_vector_scale b x) =
      p88_vector_scale (p88_field_mul F a b) x;
  p88_scale_one :
    forall x, p88_vector_scale (p88_field_one F) x = x
}.

Record putnam_1988_a6_linear_map
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F) : Type := {
  p88_linear_apply :
    p88_vector_carrier F V -> p88_vector_carrier F V;
  p88_linear_add :
    forall x y,
      p88_linear_apply (p88_vector_add F V x y) =
      p88_vector_add F V (p88_linear_apply x) (p88_linear_apply y);
  p88_linear_scale :
    forall a x,
      p88_linear_apply (p88_vector_scale F V a x) =
      p88_vector_scale F V a (p88_linear_apply x)
}.

Fixpoint putnam_1988_a6_linear_combination
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (coefficients : list (p88_field_carrier F))
    (vectors : list (p88_vector_carrier F V))
    : p88_vector_carrier F V :=
  match coefficients, vectors with
  | a :: coefficients', v :: vectors' =>
      p88_vector_add F V
        (p88_vector_scale F V a v)
        (putnam_1988_a6_linear_combination
          F V coefficients' vectors')
  | _, _ => p88_vector_zero F V
  end.

Definition putnam_1988_a6_linearly_independent
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (vectors : list (p88_vector_carrier F V)) : Prop :=
  forall coefficients : list (p88_field_carrier F),
    length coefficients = length vectors ->
    putnam_1988_a6_linear_combination F V coefficients vectors =
      p88_vector_zero F V ->
    Forall (fun coefficient => coefficient = p88_field_zero F) coefficients.

Definition putnam_1988_a6_spans
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (vectors : list (p88_vector_carrier F V)) : Prop :=
  forall v : p88_vector_carrier F V,
    exists coefficients : list (p88_field_carrier F),
      length coefficients = length vectors /\
      putnam_1988_a6_linear_combination F V coefficients vectors = v.

Definition putnam_1988_a6_exact_dimension
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (n : nat) : Prop :=
  exists basis : list (p88_vector_carrier F V),
    length basis = n /\
    putnam_1988_a6_linearly_independent F V basis /\
    putnam_1988_a6_spans F V basis.

Definition putnam_1988_a6_has_cardinality
    {A : Type} (members : A -> Prop) (n : nat) : Prop :=
  exists elements : list A,
    NoDup elements /\
    length elements = n /\
    forall x : A, In x elements <-> members x.

Definition putnam_1988_a6_is_eigenvector
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (A : putnam_1988_a6_linear_map F V)
    (v : p88_vector_carrier F V) : Prop :=
  v <> p88_vector_zero F V /\
  exists eigenvalue : p88_field_carrier F,
    p88_linear_apply F V A v =
      p88_vector_scale F V eigenvalue v.

Definition putnam_1988_a6_every_n_independent
    (F : putnam_1988_a6_field)
    (V : putnam_1988_a6_vector_space F)
    (n : nat)
    (eigenvectors : p88_vector_carrier F V -> Prop) : Prop :=
  forall vectors : list (p88_vector_carrier F V),
    length vectors = n ->
    NoDup vectors ->
    (forall v, In v vectors -> eigenvectors v) ->
    putnam_1988_a6_linearly_independent F V vectors.

Definition putnam_1988_a6_solution : Prop := True.

Theorem putnam_1988_a6 :
  (forall
      (F : putnam_1988_a6_field)
      (V : putnam_1988_a6_vector_space F)
      (n : nat)
      (A : putnam_1988_a6_linear_map F V)
      (eigenvectors : p88_vector_carrier F V -> Prop),
    putnam_1988_a6_exact_dimension F V n /\
    (forall v,
      eigenvectors v ->
      putnam_1988_a6_is_eigenvector F V A v) /\
    putnam_1988_a6_has_cardinality eigenvectors (S n) /\
    putnam_1988_a6_every_n_independent F V n eigenvectors ->
    exists scalar : p88_field_carrier F,
      forall v : p88_vector_carrier F V,
        p88_linear_apply F V A v =
        p88_vector_scale F V scalar v)
  <-> putnam_1988_a6_solution.
Admitted.
