(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1966978
  (thousand-theorems__rocq__Q1966978), "Lévy continuity theorem": weak
  convergence of Borel probability measures on a finite-dimensional real
  inner-product space is equivalent to pointwise convergence of their
  characteristic functions. This file contains no proof.
*)

From Stdlib Require Import Reals PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1966978_set (A : Type) : Type := A -> Prop.

Definition q1966978_empty {A : Type} : q1966978_set A :=
  fun _ => False.

Definition q1966978_full {A : Type} : q1966978_set A :=
  fun _ => True.

Definition q1966978_complement {A : Type}
    (U : q1966978_set A) : q1966978_set A :=
  fun x => ~ U x.

Definition q1966978_countable_union {A : Type}
    (U : nat -> q1966978_set A) : q1966978_set A :=
  fun x => exists n : nat, U n x.

Definition q1966978_preimage {A B : Type}
    (f : A -> B) (U : q1966978_set B) : q1966978_set A :=
  fun x => U (f x).

Definition q1966978_same_set {A : Type}
    (U W : q1966978_set A) : Prop :=
  forall x : A, U x <-> W x.

Definition q1966978_disjoint {A : Type}
    (U W : q1966978_set A) : Prop :=
  forall x : A, ~ (U x /\ W x).

Definition q1966978_pairwise_disjoint {A : Type}
    (U : nat -> q1966978_set A) : Prop :=
  forall i j : nat,
    i <> j -> q1966978_disjoint (U i) (U j).

Fixpoint q1966978_real_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q1966978_real_partial_sum u k + u k
  end.

Definition q1966978_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Record q1966978_complex : Type := {
  q1966978_re : R;
  q1966978_im : R
}.

Definition q1966978_complex_distance
    (z w : q1966978_complex) : R :=
  sqrt
    ((q1966978_re z - q1966978_re w) ^ 2 +
     (q1966978_im z - q1966978_im w) ^ 2).

Definition q1966978_complex_sequence_converges
    (u : nat -> q1966978_complex)
    (limit : q1966978_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1966978_complex_distance (u n) limit < epsilon.

Record q1966978_real_inner_product_space (E : Type) : Type := {
  q1966978_zero : E;
  q1966978_add : E -> E -> E;
  q1966978_neg : E -> E;
  q1966978_smul : R -> E -> E;
  q1966978_inner : E -> E -> R;
  q1966978_add_assoc :
    forall x y z : E,
      q1966978_add x (q1966978_add y z) =
      q1966978_add (q1966978_add x y) z;
  q1966978_add_comm :
    forall x y : E, q1966978_add x y = q1966978_add y x;
  q1966978_zero_add :
    forall x : E, q1966978_add q1966978_zero x = x;
  q1966978_neg_add :
    forall x : E, q1966978_add (q1966978_neg x) x = q1966978_zero;
  q1966978_one_smul :
    forall x : E, q1966978_smul 1 x = x;
  q1966978_mul_smul :
    forall (a b : R) (x : E),
      q1966978_smul (a * b) x =
      q1966978_smul a (q1966978_smul b x);
  q1966978_add_smul :
    forall (a b : R) (x : E),
      q1966978_smul (a + b) x =
      q1966978_add (q1966978_smul a x) (q1966978_smul b x);
  q1966978_smul_add :
    forall (a : R) (x y : E),
      q1966978_smul a (q1966978_add x y) =
      q1966978_add (q1966978_smul a x) (q1966978_smul a y);
  q1966978_zero_smul :
    forall x : E, q1966978_smul 0 x = q1966978_zero;
  q1966978_smul_zero :
    forall a : R, q1966978_smul a q1966978_zero = q1966978_zero;
  q1966978_neg_eq_smul :
    forall x : E, q1966978_neg x = q1966978_smul (-1) x;
  q1966978_inner_add_left :
    forall x y z : E,
      q1966978_inner (q1966978_add x y) z =
      q1966978_inner x z + q1966978_inner y z;
  q1966978_inner_smul_left :
    forall (a : R) (x y : E),
      q1966978_inner (q1966978_smul a x) y =
      a * q1966978_inner x y;
  q1966978_inner_symm :
    forall x y : E, q1966978_inner x y = q1966978_inner y x;
  q1966978_inner_nonnegative :
    forall x : E, 0 <= q1966978_inner x x;
  q1966978_inner_eq_zero :
    forall x : E,
      q1966978_inner x x = 0 <-> x = q1966978_zero;
  q1966978_finite_orthonormal_basis :
    exists (dimension : nat) (basis : nat -> E),
      (forall i j : nat,
        (i < dimension)%nat ->
        (j < dimension)%nat ->
        q1966978_inner (basis i) (basis j) =
          if Nat.eq_dec i j then 1 else 0) /\
      forall x : E,
        x =
        (fix sum (n : nat) : E :=
          match n with
          | O => q1966978_zero
          | S k =>
              q1966978_add
                (sum k)
                (q1966978_smul
                  (q1966978_inner x (basis k))
                  (basis k))
          end) dimension
}.

Arguments q1966978_zero {E} _.
Arguments q1966978_add {E} _ _ _.
Arguments q1966978_neg {E} _ _.
Arguments q1966978_smul {E} _ _ _.
Arguments q1966978_inner {E} _ _ _.

Definition q1966978_sub {E : Type}
    (V : q1966978_real_inner_product_space E)
    (x y : E) : E :=
  q1966978_add V x (q1966978_neg V y).

Definition q1966978_norm {E : Type}
    (V : q1966978_real_inner_product_space E)
    (x : E) : R :=
  sqrt (q1966978_inner V x x).

Definition q1966978_metric_open {E : Type}
    (V : q1966978_real_inner_product_space E)
    (U : q1966978_set E) : Prop :=
  forall x : E,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : E,
        q1966978_norm V (q1966978_sub V y x) < epsilon ->
        U y.

Inductive q1966978_borel {E : Type}
    (V : q1966978_real_inner_product_space E)
    : q1966978_set E -> Prop :=
| q1966978_borel_open :
    forall U : q1966978_set E,
      q1966978_metric_open V U ->
      q1966978_borel V U
| q1966978_borel_extensional :
    forall U W : q1966978_set E,
      q1966978_borel V U ->
      q1966978_same_set U W ->
      q1966978_borel V W
| q1966978_borel_complement :
    forall U : q1966978_set E,
      q1966978_borel V U ->
      q1966978_borel V (q1966978_complement U)
| q1966978_borel_countable_union :
    forall U : nat -> q1966978_set E,
      (forall n : nat, q1966978_borel V (U n)) ->
      q1966978_borel V (q1966978_countable_union U).

Definition q1966978_real_open
    (U : q1966978_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Inductive q1966978_real_borel : q1966978_set R -> Prop :=
| q1966978_real_borel_open :
    forall U : q1966978_set R,
      q1966978_real_open U ->
      q1966978_real_borel U
| q1966978_real_borel_extensional :
    forall U W : q1966978_set R,
      q1966978_real_borel U ->
      q1966978_same_set U W ->
      q1966978_real_borel W
| q1966978_real_borel_complement :
    forall U : q1966978_set R,
      q1966978_real_borel U ->
      q1966978_real_borel (q1966978_complement U)
| q1966978_real_borel_countable_union :
    forall U : nat -> q1966978_set R,
      (forall n : nat, q1966978_real_borel (U n)) ->
      q1966978_real_borel (q1966978_countable_union U).

Definition q1966978_measurable_real_function {E : Type}
    (V : q1966978_real_inner_product_space E)
    (f : E -> R) : Prop :=
  forall U : q1966978_set R,
    q1966978_real_borel U ->
    q1966978_borel V (q1966978_preimage f U).

Definition q1966978_continuous_real_function {E : Type}
    (V : q1966978_real_inner_product_space E)
    (f : E -> R) : Prop :=
  forall (x : E) (epsilon : R),
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : E,
        q1966978_norm V (q1966978_sub V y x) < delta ->
        Rabs (f y - f x) < epsilon.

Definition q1966978_bounded {E : Type}
    (f : E -> R) : Prop :=
  exists C : R,
    0 <= C /\ forall x : E, Rabs (f x) <= C.

Definition q1966978_nonnegative {E : Type}
    (f : E -> R) : Prop :=
  forall x : E, 0 <= f x.

Definition q1966978_increasing {E : Type}
    (f : nat -> E -> R) : Prop :=
  forall (n : nat) (x : E), f n x <= f (S n) x.

Definition q1966978_is_indicator {E : Type}
    (U : q1966978_set E) (f : E -> R) : Prop :=
  forall x : E,
    (U x /\ f x = 1) \/ (~ U x /\ f x = 0).

Record q1966978_probability_measure
    (E : Type) (V : q1966978_real_inner_product_space E) : Type := {
  q1966978_mass : q1966978_set E -> R;
  q1966978_integral : (E -> R) -> R;
  q1966978_mass_extensional :
    forall U W : q1966978_set E,
      q1966978_same_set U W ->
      q1966978_mass U = q1966978_mass W;
  q1966978_mass_empty :
    q1966978_mass q1966978_empty = 0;
  q1966978_mass_full :
    q1966978_mass q1966978_full = 1;
  q1966978_mass_nonnegative :
    forall U : q1966978_set E,
      q1966978_borel V U ->
      0 <= q1966978_mass U;
  q1966978_mass_countably_additive :
    forall U : nat -> q1966978_set E,
      (forall n : nat, q1966978_borel V (U n)) ->
      q1966978_pairwise_disjoint U ->
      q1966978_real_sequence_converges
        (fun n =>
          q1966978_real_partial_sum
            (fun k => q1966978_mass (U k)) n)
        (q1966978_mass (q1966978_countable_union U));
  q1966978_integral_extensional :
    forall f g : E -> R,
      q1966978_measurable_real_function V f ->
      q1966978_measurable_real_function V g ->
      q1966978_bounded f ->
      q1966978_bounded g ->
      (forall x : E, f x = g x) ->
      q1966978_integral f = q1966978_integral g;
  q1966978_integral_indicator :
    forall (U : q1966978_set E) (f : E -> R),
      q1966978_borel V U ->
      q1966978_is_indicator U f ->
      q1966978_integral f = q1966978_mass U;
  q1966978_integral_add :
    forall f g : E -> R,
      q1966978_measurable_real_function V f ->
      q1966978_measurable_real_function V g ->
      q1966978_bounded f ->
      q1966978_bounded g ->
      q1966978_integral (fun x => f x + g x) =
      q1966978_integral f + q1966978_integral g;
  q1966978_integral_scale :
    forall (a : R) (f : E -> R),
      q1966978_measurable_real_function V f ->
      q1966978_bounded f ->
      q1966978_integral (fun x => a * f x) =
      a * q1966978_integral f;
  q1966978_integral_nonnegative :
    forall f : E -> R,
      q1966978_measurable_real_function V f ->
      q1966978_bounded f ->
      q1966978_nonnegative f ->
      0 <= q1966978_integral f;
  q1966978_integral_monotone_convergence :
    forall (f : nat -> E -> R) (g : E -> R),
      (forall n : nat, q1966978_measurable_real_function V (f n)) ->
      q1966978_measurable_real_function V g ->
      (forall n : nat, q1966978_bounded (f n)) ->
      q1966978_bounded g ->
      (forall n : nat, q1966978_nonnegative (f n)) ->
      q1966978_increasing f ->
      (forall x : E,
        q1966978_real_sequence_converges
          (fun n => f n x) (g x)) ->
      q1966978_real_sequence_converges
        (fun n => q1966978_integral (f n))
        (q1966978_integral g)
}.

Arguments q1966978_probability_measure E V : clear implicits.
Arguments q1966978_mass {E V} _ _.
Arguments q1966978_integral {E V} _ _.

Definition q1966978_weak_tendsto {E : Type}
    {V : q1966978_real_inner_product_space E}
    (mu : nat -> q1966978_probability_measure E V)
    (mu0 : q1966978_probability_measure E V) : Prop :=
  forall f : E -> R,
    q1966978_continuous_real_function V f ->
    q1966978_bounded f ->
    q1966978_real_sequence_converges
      (fun n => q1966978_integral (mu n) f)
      (q1966978_integral mu0 f).

Definition q1966978_characteristic_function {E : Type}
    {V : q1966978_real_inner_product_space E}
    (mu : q1966978_probability_measure E V)
    (t : E) : q1966978_complex :=
  {|
    q1966978_re :=
      q1966978_integral mu
        (fun x => cos (q1966978_inner V x t));
    q1966978_im :=
      q1966978_integral mu
        (fun x => sin (q1966978_inner V x t))
  |}.

Theorem q1966978_levy_continuity_theorem :
  forall (E : Type)
         (V : q1966978_real_inner_product_space E)
         (mu : nat -> q1966978_probability_measure E V)
         (mu0 : q1966978_probability_measure E V),
    q1966978_weak_tendsto mu mu0 <->
    forall t : E,
      q1966978_complex_sequence_converges
        (fun n => q1966978_characteristic_function (mu n) t)
        (q1966978_characteristic_function mu0 t).
Admitted.
