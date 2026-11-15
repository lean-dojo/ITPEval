(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527241
  (thousand-theorems__rocq__Q3527241), "Krull's principal ideal theorem":
  in a commutative Noetherian ring, every prime ideal minimal over a principal
  ideal has height at most one. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q3527241_commutative_ring (R : Type) : Type := {
  q3527241_zero : R;
  q3527241_one : R;
  q3527241_add : R -> R -> R;
  q3527241_mul : R -> R -> R;
  q3527241_neg : R -> R;
  q3527241_add_assoc :
    forall x y z : R,
      q3527241_add x (q3527241_add y z) =
      q3527241_add (q3527241_add x y) z;
  q3527241_add_comm :
    forall x y : R,
      q3527241_add x y = q3527241_add y x;
  q3527241_add_zero :
    forall x : R,
      q3527241_add x q3527241_zero = x;
  q3527241_add_neg :
    forall x : R,
      q3527241_add x (q3527241_neg x) = q3527241_zero;
  q3527241_mul_assoc :
    forall x y z : R,
      q3527241_mul x (q3527241_mul y z) =
      q3527241_mul (q3527241_mul x y) z;
  q3527241_mul_comm :
    forall x y : R,
      q3527241_mul x y = q3527241_mul y x;
  q3527241_mul_one :
    forall x : R,
      q3527241_mul x q3527241_one = x;
  q3527241_left_distrib :
    forall x y z : R,
      q3527241_mul x (q3527241_add y z) =
      q3527241_add
        (q3527241_mul x y) (q3527241_mul x z)
}.

Arguments q3527241_zero {R} _.
Arguments q3527241_one {R} _.
Arguments q3527241_add {R} _ _ _.
Arguments q3527241_mul {R} _ _ _.
Arguments q3527241_neg {R} _ _.

Record q3527241_ideal
    {R : Type}
    (CR : q3527241_commutative_ring R) : Type := {
  q3527241_ideal_mem : R -> Prop;
  q3527241_ideal_zero :
    q3527241_ideal_mem (q3527241_zero CR);
  q3527241_ideal_add :
    forall x y : R,
      q3527241_ideal_mem x ->
      q3527241_ideal_mem y ->
      q3527241_ideal_mem (q3527241_add CR x y);
  q3527241_ideal_neg :
    forall x : R,
      q3527241_ideal_mem x ->
      q3527241_ideal_mem (q3527241_neg CR x);
  q3527241_ideal_mul :
    forall a x : R,
      q3527241_ideal_mem x ->
      q3527241_ideal_mem (q3527241_mul CR a x)
}.

Arguments q3527241_ideal_mem {R CR} _ _.

Definition q3527241_ideal_le
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (I J : @q3527241_ideal R CR) : Prop :=
  forall x : R,
    q3527241_ideal_mem I x ->
    q3527241_ideal_mem J x.

Definition q3527241_ideal_lt
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (I J : @q3527241_ideal R CR) : Prop :=
  q3527241_ideal_le I J /\ ~ q3527241_ideal_le J I.

Definition q3527241_is_prime
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (P : @q3527241_ideal R CR) : Prop :=
  ~ q3527241_ideal_mem P (q3527241_one CR) /\
  forall x y : R,
    q3527241_ideal_mem P (q3527241_mul CR x y) ->
    q3527241_ideal_mem P x \/ q3527241_ideal_mem P y.

Fixpoint q3527241_linear_combination
    {R : Type}
    (CR : q3527241_commutative_ring R)
    (coefficients generators : list R) : R :=
  match coefficients, generators with
  | coefficient :: coefficient_rest, generator :: generator_rest =>
      q3527241_add CR
        (q3527241_mul CR coefficient generator)
        (q3527241_linear_combination
          CR coefficient_rest generator_rest)
  | _, _ => q3527241_zero CR
  end.

Definition q3527241_generated_by
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (generators : list R)
    (I : @q3527241_ideal R CR) : Prop :=
  forall x : R,
    q3527241_ideal_mem I x <->
    exists coefficients : list R,
      length coefficients = length generators /\
      x = q3527241_linear_combination CR coefficients generators.

Definition q3527241_is_noetherian
    {R : Type}
    {CR : q3527241_commutative_ring R} : Prop :=
  forall I : @q3527241_ideal R CR,
    exists generators : list R,
      q3527241_generated_by generators I.

Definition q3527241_is_principal
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (I : @q3527241_ideal R CR) : Prop :=
  exists generator : R,
    forall x : R,
      q3527241_ideal_mem I x <->
      exists coefficient : R,
        x = q3527241_mul CR coefficient generator.

Definition q3527241_is_minimal_prime_over
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (I P : @q3527241_ideal R CR) : Prop :=
  q3527241_is_prime P /\
  q3527241_ideal_le I P /\
  forall Q : @q3527241_ideal R CR,
    q3527241_is_prime Q ->
    q3527241_ideal_le I Q ->
    q3527241_ideal_le Q P ->
    q3527241_ideal_le P Q.

Definition q3527241_height_le_one
    {R : Type}
    {CR : q3527241_commutative_ring R}
    (P : @q3527241_ideal R CR) : Prop :=
  forall Q0 Q1 : @q3527241_ideal R CR,
    q3527241_is_prime Q0 ->
    q3527241_is_prime Q1 ->
    q3527241_ideal_lt Q0 Q1 ->
    q3527241_ideal_lt Q1 P ->
    False.

Theorem Ideal_height_le_one_of_isPrincipal_of_mem_minimalPrimes :
  forall (R : Type)
         (CR : q3527241_commutative_ring R),
    @q3527241_is_noetherian R CR ->
    forall I : @q3527241_ideal R CR,
      q3527241_is_principal I ->
      forall P : @q3527241_ideal R CR,
        q3527241_is_minimal_prime_over I P ->
        q3527241_height_le_one P.
Admitted.
