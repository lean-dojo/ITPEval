(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656645
  (thousand-theorems__rocq__Q656645), "Hilbert's basis theorem": for an
  arbitrary commutative ring, if every ideal of the coefficient ring is
  finitely generated, then every ideal of its univariate polynomial ring is
  finitely generated. This file contains no proof.
*)

From Stdlib Require Import List Arith Bool.

Set Universe Polymorphism.
Set Implicit Arguments.

Import ListNotations.

Record q656645_commutative_ring (R : Type) : Type := {
  q656645_zero : R;
  q656645_one : R;
  q656645_add : R -> R -> R;
  q656645_mul : R -> R -> R;
  q656645_neg : R -> R;
  q656645_add_assoc :
    forall x y z : R,
      q656645_add x (q656645_add y z) =
      q656645_add (q656645_add x y) z;
  q656645_add_comm :
    forall x y : R,
      q656645_add x y = q656645_add y x;
  q656645_add_zero :
    forall x : R,
      q656645_add x q656645_zero = x;
  q656645_add_neg :
    forall x : R,
      q656645_add x (q656645_neg x) = q656645_zero;
  q656645_mul_assoc :
    forall x y z : R,
      q656645_mul x (q656645_mul y z) =
      q656645_mul (q656645_mul x y) z;
  q656645_mul_comm :
    forall x y : R,
      q656645_mul x y = q656645_mul y x;
  q656645_mul_one :
    forall x : R,
      q656645_mul x q656645_one = x;
  q656645_left_distrib :
    forall x y z : R,
      q656645_mul x (q656645_add y z) =
      q656645_add
        (q656645_mul x y) (q656645_mul x z)
}.

Arguments q656645_zero {R} _.
Arguments q656645_one {R} _.
Arguments q656645_add {R} _ _ _.
Arguments q656645_mul {R} _ _ _.
Arguments q656645_neg {R} _ _.

Record q656645_ideal
    {R : Type}
    (CR : q656645_commutative_ring R) : Type := {
  q656645_ideal_mem : R -> Prop;
  q656645_ideal_zero :
    q656645_ideal_mem (q656645_zero CR);
  q656645_ideal_add :
    forall x y : R,
      q656645_ideal_mem x ->
      q656645_ideal_mem y ->
      q656645_ideal_mem (q656645_add CR x y);
  q656645_ideal_neg :
    forall x : R,
      q656645_ideal_mem x ->
      q656645_ideal_mem (q656645_neg CR x);
  q656645_ideal_mul :
    forall a x : R,
      q656645_ideal_mem x ->
      q656645_ideal_mem (q656645_mul CR a x)
}.

Arguments q656645_ideal_mem {R CR} _ _.

Fixpoint q656645_linear_combination
    {R : Type}
    (CR : q656645_commutative_ring R)
    (coefficients generators : list R) : R :=
  match coefficients, generators with
  | coefficient :: coefficient_rest, generator :: generator_rest =>
      q656645_add CR
        (q656645_mul CR coefficient generator)
        (q656645_linear_combination
          CR coefficient_rest generator_rest)
  | _, _ => q656645_zero CR
  end.

Definition q656645_generated_by
    {R : Type}
    {CR : q656645_commutative_ring R}
    (generators : list R)
    (I : @q656645_ideal R CR) : Prop :=
  forall x : R,
    q656645_ideal_mem I x <->
    exists coefficients : list R,
      length coefficients = length generators /\
      x = q656645_linear_combination CR coefficients generators.

Definition q656645_is_noetherian
    {R : Type}
    {CR : q656645_commutative_ring R} : Prop :=
  forall I : @q656645_ideal R CR,
    exists generators : list R,
      q656645_generated_by generators I.

Definition q656645_polynomial (R : Type) : Type :=
  list (nat * R).

Fixpoint q656645_polynomial_coefficient
    {R : Type}
    (CR : q656645_commutative_ring R)
    (p : q656645_polynomial R)
    (n : nat) : R :=
  match p with
  | [] => q656645_zero CR
  | (degree, coefficient) :: rest =>
      if Nat.eqb degree n
      then q656645_add CR coefficient
        (q656645_polynomial_coefficient CR rest n)
      else q656645_polynomial_coefficient CR rest n
  end.

Definition q656645_polynomial_equiv
    {R : Type}
    (CR : q656645_commutative_ring R)
    (p q : q656645_polynomial R) : Prop :=
  forall n : nat,
    q656645_polynomial_coefficient CR p n =
    q656645_polynomial_coefficient CR q n.

Definition q656645_polynomial_zero
    {R : Type} : q656645_polynomial R :=
  [].

Definition q656645_polynomial_one
    {R : Type}
    (CR : q656645_commutative_ring R) : q656645_polynomial R :=
  [(0, q656645_one CR)].

Definition q656645_polynomial_add
    {R : Type}
    (p q : q656645_polynomial R) : q656645_polynomial R :=
  p ++ q.

Definition q656645_polynomial_neg
    {R : Type}
    (CR : q656645_commutative_ring R)
    (p : q656645_polynomial R) : q656645_polynomial R :=
  map
    (fun term => (fst term, q656645_neg CR (snd term)))
    p.

Definition q656645_term_mul
    {R : Type}
    (CR : q656645_commutative_ring R)
    (left right : nat * R) : nat * R :=
  (fst left + fst right,
   q656645_mul CR (snd left) (snd right)).

Definition q656645_polynomial_mul
    {R : Type}
    (CR : q656645_commutative_ring R)
    (p q : q656645_polynomial R) : q656645_polynomial R :=
  flat_map
    (fun left => map (q656645_term_mul CR left) q)
    p.

Record q656645_polynomial_ideal
    {R : Type}
    (CR : q656645_commutative_ring R) : Type := {
  q656645_polynomial_ideal_mem :
    q656645_polynomial R -> Prop;
  q656645_polynomial_ideal_respects :
    forall p q : q656645_polynomial R,
      q656645_polynomial_equiv CR p q ->
      (q656645_polynomial_ideal_mem p <->
       q656645_polynomial_ideal_mem q);
  q656645_polynomial_ideal_zero :
    q656645_polynomial_ideal_mem q656645_polynomial_zero;
  q656645_polynomial_ideal_add :
    forall p q : q656645_polynomial R,
      q656645_polynomial_ideal_mem p ->
      q656645_polynomial_ideal_mem q ->
      q656645_polynomial_ideal_mem
        (q656645_polynomial_add p q);
  q656645_polynomial_ideal_neg :
    forall p : q656645_polynomial R,
      q656645_polynomial_ideal_mem p ->
      q656645_polynomial_ideal_mem
        (q656645_polynomial_neg CR p);
  q656645_polynomial_ideal_mul :
    forall a p : q656645_polynomial R,
      q656645_polynomial_ideal_mem p ->
      q656645_polynomial_ideal_mem
        (q656645_polynomial_mul CR a p)
}.

Arguments q656645_polynomial_ideal_mem {R CR} _ _.

Fixpoint q656645_polynomial_linear_combination
    {R : Type}
    (CR : q656645_commutative_ring R)
    (coefficients generators : list (q656645_polynomial R)) :
    q656645_polynomial R :=
  match coefficients, generators with
  | coefficient :: coefficient_rest, generator :: generator_rest =>
      q656645_polynomial_add
        (q656645_polynomial_mul CR coefficient generator)
        (q656645_polynomial_linear_combination
          CR coefficient_rest generator_rest)
  | _, _ => q656645_polynomial_zero
  end.

Definition q656645_polynomial_generated_by
    {R : Type}
    {CR : q656645_commutative_ring R}
    (generators : list (q656645_polynomial R))
    (I : @q656645_polynomial_ideal R CR) : Prop :=
  forall p : q656645_polynomial R,
    q656645_polynomial_ideal_mem I p <->
    exists coefficients : list (q656645_polynomial R),
      length coefficients = length generators /\
      q656645_polynomial_equiv CR p
        (q656645_polynomial_linear_combination
          CR coefficients generators).

Definition q656645_polynomial_is_noetherian
    {R : Type}
    {CR : q656645_commutative_ring R} : Prop :=
  forall I : @q656645_polynomial_ideal R CR,
    exists generators : list (q656645_polynomial R),
      q656645_polynomial_generated_by generators I.

Theorem Polynomial_isNoetherianRing :
  forall (R : Type)
         (CR : q656645_commutative_ring R),
    @q656645_is_noetherian R CR ->
    @q656645_polynomial_is_noetherian R CR.
Admitted.
