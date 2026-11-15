(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2379132
  (thousand-theorems__rocq__Q2379132), "Going-up and going-down theorems".
  It states the two indexed going-up results, the prime-spectrum
  characterization of going-down, and the localized-spectrum surjectivity
  criterion. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Import ListNotations.

Record q2379132_commutative_ring (A : Type) : Type := {
  q2379132_zero : A;
  q2379132_one : A;
  q2379132_add : A -> A -> A;
  q2379132_mul : A -> A -> A;
  q2379132_neg : A -> A;
  q2379132_add_assoc :
    forall x y z : A,
      q2379132_add x (q2379132_add y z) =
      q2379132_add (q2379132_add x y) z;
  q2379132_add_comm :
    forall x y : A,
      q2379132_add x y = q2379132_add y x;
  q2379132_add_zero :
    forall x : A,
      q2379132_add x q2379132_zero = x;
  q2379132_add_neg :
    forall x : A,
      q2379132_add x (q2379132_neg x) = q2379132_zero;
  q2379132_mul_assoc :
    forall x y z : A,
      q2379132_mul x (q2379132_mul y z) =
      q2379132_mul (q2379132_mul x y) z;
  q2379132_mul_comm :
    forall x y : A,
      q2379132_mul x y = q2379132_mul y x;
  q2379132_mul_one :
    forall x : A,
      q2379132_mul x q2379132_one = x;
  q2379132_left_distrib :
    forall x y z : A,
      q2379132_mul x (q2379132_add y z) =
      q2379132_add
        (q2379132_mul x y) (q2379132_mul x z)
}.

Arguments q2379132_zero {A} _.
Arguments q2379132_one {A} _.
Arguments q2379132_add {A} _ _ _.
Arguments q2379132_mul {A} _ _ _.
Arguments q2379132_neg {A} _ _.

Record q2379132_integral_domain
    {A : Type}
    (RA : q2379132_commutative_ring A) : Type := {
  q2379132_domain_nontrivial :
    q2379132_zero RA <> q2379132_one RA;
  q2379132_domain_no_zero_divisors :
    forall x y : A,
      q2379132_mul RA x y = q2379132_zero RA ->
      x = q2379132_zero RA \/ y = q2379132_zero RA
}.

Record q2379132_ring_hom
    {R S : Type}
    (RR : q2379132_commutative_ring R)
    (RS : q2379132_commutative_ring S) : Type := {
  q2379132_map : R -> S;
  q2379132_map_zero :
    q2379132_map (q2379132_zero RR) = q2379132_zero RS;
  q2379132_map_one :
    q2379132_map (q2379132_one RR) = q2379132_one RS;
  q2379132_map_add :
    forall x y : R,
      q2379132_map (q2379132_add RR x y) =
      q2379132_add RS (q2379132_map x) (q2379132_map y);
  q2379132_map_mul :
    forall x y : R,
      q2379132_map (q2379132_mul RR x y) =
      q2379132_mul RS (q2379132_map x) (q2379132_map y)
}.

Arguments q2379132_map {R S RR RS} _ _.

Record q2379132_ideal
    {A : Type}
    (RA : q2379132_commutative_ring A) : Type := {
  q2379132_ideal_mem : A -> Prop;
  q2379132_ideal_zero :
    q2379132_ideal_mem (q2379132_zero RA);
  q2379132_ideal_add :
    forall x y : A,
      q2379132_ideal_mem x ->
      q2379132_ideal_mem y ->
      q2379132_ideal_mem (q2379132_add RA x y);
  q2379132_ideal_neg :
    forall x : A,
      q2379132_ideal_mem x ->
      q2379132_ideal_mem (q2379132_neg RA x);
  q2379132_ideal_mul :
    forall a x : A,
      q2379132_ideal_mem x ->
      q2379132_ideal_mem (q2379132_mul RA a x)
}.

Arguments q2379132_ideal_mem {A RA} _ _.

Definition q2379132_is_prime_ideal
    {A : Type}
    {RA : q2379132_commutative_ring A}
    (I : @q2379132_ideal A RA) : Prop :=
  ~ q2379132_ideal_mem I (q2379132_one RA) /\
  forall x y : A,
    q2379132_ideal_mem I (q2379132_mul RA x y) ->
    q2379132_ideal_mem I x \/ q2379132_ideal_mem I y.

Fixpoint q2379132_polynomial_eval
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (coefficients : list R)
    (x : S) : S :=
  match coefficients with
  | [] => q2379132_zero RS
  | coefficient :: rest =>
      q2379132_add RS
        (q2379132_map f coefficient)
        (q2379132_mul RS x
          (q2379132_polynomial_eval f rest x))
  end.

Definition q2379132_is_integral_hom
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS) : Prop :=
  forall x : S,
    exists coefficients : list R,
      q2379132_polynomial_eval
        f (coefficients ++ [q2379132_one RR]) x =
      q2379132_zero RS.

Definition q2379132_kernel_contained
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (P : @q2379132_ideal R RR) : Prop :=
  forall x : R,
    q2379132_map f x = q2379132_zero RS ->
    q2379132_ideal_mem P x.

Definition q2379132_contraction_equal
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (Q : @q2379132_ideal S RS)
    (P : @q2379132_ideal R RR) : Prop :=
  forall x : R,
    q2379132_ideal_mem Q (q2379132_map f x) <->
    q2379132_ideal_mem P x.

Definition q2379132_ideal_included
    {A : Type}
    {RA : q2379132_commutative_ring A}
    (I J : @q2379132_ideal A RA) : Prop :=
  forall x : A,
    q2379132_ideal_mem I x ->
    q2379132_ideal_mem J x.

Definition q2379132_ideal_below_contraction
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (P : @q2379132_ideal R RR)
    (Q : @q2379132_ideal S RS) : Prop :=
  forall x : R,
    q2379132_ideal_mem P x ->
    q2379132_ideal_mem Q (q2379132_map f x).

Definition q2379132_contraction_included_in_ideal
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (Q : @q2379132_ideal S RS)
    (P : @q2379132_ideal R RR) : Prop :=
  forall x : R,
    q2379132_ideal_mem Q (q2379132_map f x) ->
    q2379132_ideal_mem P x.

Definition q2379132_has_going_down
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS) : Prop :=
  forall p q : @q2379132_ideal R RR,
    q2379132_is_prime_ideal p ->
    q2379132_is_prime_ideal q ->
    q2379132_ideal_included p q ->
    forall Q : @q2379132_ideal S RS,
      q2379132_is_prime_ideal Q ->
      q2379132_contraction_equal f Q q ->
      exists P : @q2379132_ideal S RS,
        q2379132_is_prime_ideal P /\
        q2379132_ideal_included P Q /\
        q2379132_contraction_equal f P p.

Definition q2379132_generalizing_prime_spectrum_comap
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS) : Prop :=
  forall Q : @q2379132_ideal S RS,
    q2379132_is_prime_ideal Q ->
    forall p : @q2379132_ideal R RR,
      q2379132_is_prime_ideal p ->
      q2379132_ideal_below_contraction f p Q ->
      exists P : @q2379132_ideal S RS,
        q2379132_is_prime_ideal P /\
        q2379132_ideal_included P Q /\
        q2379132_contraction_equal f P p.

Definition q2379132_local_prime_spectrum_comap_surjective
    {R S : Type}
    {RR : q2379132_commutative_ring R}
    {RS : q2379132_commutative_ring S}
    (f : q2379132_ring_hom RR RS)
    (Q : @q2379132_ideal S RS) : Prop :=
  forall p : @q2379132_ideal R RR,
    q2379132_is_prime_ideal p ->
    q2379132_ideal_below_contraction f p Q ->
    exists P : @q2379132_ideal S RS,
      q2379132_is_prime_ideal P /\
      q2379132_ideal_included P Q /\
      q2379132_contraction_equal f P p.

Theorem Ideal_exists_ideal_over_prime_of_isIntegral_of_isDomain :
  forall
    (R S : Type)
    (RR : q2379132_commutative_ring R)
    (RS : q2379132_commutative_ring S)
    (DS : q2379132_integral_domain RS)
    (f : q2379132_ring_hom RR RS)
    (P : @q2379132_ideal R RR),
    q2379132_is_integral_hom f ->
    q2379132_is_prime_ideal P ->
    q2379132_kernel_contained f P ->
    exists Q : @q2379132_ideal S RS,
      q2379132_is_prime_ideal Q /\
      q2379132_contraction_equal f Q P.
Admitted.

Theorem Ideal_exists_ideal_over_prime_of_isIntegral_of_isPrime :
  forall
    (R S : Type)
    (RR : q2379132_commutative_ring R)
    (RS : q2379132_commutative_ring S)
    (f : q2379132_ring_hom RR RS)
    (P : @q2379132_ideal R RR)
    (I : @q2379132_ideal S RS),
    q2379132_is_integral_hom f ->
    q2379132_is_prime_ideal P ->
    q2379132_is_prime_ideal I ->
    q2379132_contraction_included_in_ideal f I P ->
    exists Q : @q2379132_ideal S RS,
      q2379132_ideal_included I Q /\
      q2379132_is_prime_ideal Q /\
      q2379132_contraction_equal f Q P.
Admitted.

Theorem Algebra_HasGoingDown_iff_generalizingMap_primeSpectrumComap :
  forall
    (R S : Type)
    (RR : q2379132_commutative_ring R)
    (RS : q2379132_commutative_ring S)
    (f : q2379132_ring_hom RR RS),
    q2379132_has_going_down f <->
    q2379132_generalizing_prime_spectrum_comap f.
Admitted.

Theorem Algebra_HasGoingDown_of_comap_localRingHom_surjective :
  forall
    (R S : Type)
    (RR : q2379132_commutative_ring R)
    (RS : q2379132_commutative_ring S)
    (f : q2379132_ring_hom RR RS),
    (forall Q : @q2379132_ideal S RS,
      q2379132_is_prime_ideal Q ->
      q2379132_local_prime_spectrum_comap_surjective f Q) ->
    q2379132_has_going_down f.
Admitted.
