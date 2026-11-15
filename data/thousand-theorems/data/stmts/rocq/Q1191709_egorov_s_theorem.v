(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1191709
  (thousand-theorems__rocq__Q1191709), "Egorov's theorem": on a measurable
  set of finite measure, an almost-everywhere convergent countable net of
  strongly measurable functions into an extended pseudometric space converges
  uniformly outside a measurable set of arbitrarily small measure. This file
  contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1191709_set (A : Type) : Type := A -> Prop.

Definition q1191709_empty {A : Type} : q1191709_set A :=
  fun _ => False.

Definition q1191709_complement {A : Type}
    (E : q1191709_set A) : q1191709_set A :=
  fun x => ~ E x.

Definition q1191709_difference {A : Type}
    (E F : q1191709_set A) : q1191709_set A :=
  fun x => E x /\ ~ F x.

Definition q1191709_countable_union {A : Type}
    (E : nat -> q1191709_set A) : q1191709_set A :=
  fun x => exists n : nat, E n x.

Definition q1191709_same_set {A : Type}
    (E F : q1191709_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1191709_subset {A : Type}
    (E F : q1191709_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q1191709_disjoint {A : Type}
    (E F : q1191709_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1191709_pairwise_disjoint {A : Type}
    (E : nat -> q1191709_set A) : Prop :=
  forall i j : nat, i <> j -> q1191709_disjoint (E i) (E j).

Inductive q1191709_ennreal : Type :=
| q1191709_ennreal_finite :
    forall value : R, 0 <= value -> q1191709_ennreal
| q1191709_ennreal_infinity : q1191709_ennreal.

Arguments q1191709_ennreal_finite value nonnegative : clear implicits.

Definition q1191709_ennreal_zero : q1191709_ennreal :=
  q1191709_ennreal_finite 0 (Rle_refl 0).

Definition q1191709_ennreal_eq
    (x y : q1191709_ennreal) : Prop :=
  match x, y with
  | q1191709_ennreal_finite a _,
    q1191709_ennreal_finite b _ => a = b
  | q1191709_ennreal_infinity,
    q1191709_ennreal_infinity => True
  | _, _ => False
  end.

Definition q1191709_ennreal_le
    (x y : q1191709_ennreal) : Prop :=
  match x, y with
  | q1191709_ennreal_finite a _,
    q1191709_ennreal_finite b _ => a <= b
  | q1191709_ennreal_finite _ _,
    q1191709_ennreal_infinity => True
  | q1191709_ennreal_infinity,
    q1191709_ennreal_finite _ _ => False
  | q1191709_ennreal_infinity,
    q1191709_ennreal_infinity => True
  end.

Definition q1191709_ennreal_lt_real
    (x : q1191709_ennreal) (bound : R) : Prop :=
  match x with
  | q1191709_ennreal_finite value _ => value < bound
  | q1191709_ennreal_infinity => False
  end.

Definition q1191709_ennreal_le_real
    (x : q1191709_ennreal) (bound : R) : Prop :=
  match x with
  | q1191709_ennreal_finite value _ => value <= bound
  | q1191709_ennreal_infinity => False
  end.

Definition q1191709_ennreal_add
    (x y : q1191709_ennreal) : q1191709_ennreal :=
  match x, y with
  | q1191709_ennreal_finite a ha,
    q1191709_ennreal_finite b hb =>
      q1191709_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1191709_ennreal_infinity
  end.

Fixpoint q1191709_ennreal_partial_sum
    (u : nat -> q1191709_ennreal)
    (n : nat) : q1191709_ennreal :=
  match n with
  | O => q1191709_ennreal_zero
  | S k =>
      q1191709_ennreal_add
        (q1191709_ennreal_partial_sum u k) (u k)
  end.

Definition q1191709_ennreal_supremum
    (values : q1191709_ennreal -> Prop)
    (bound : q1191709_ennreal) : Prop :=
  (forall value : q1191709_ennreal,
      values value -> q1191709_ennreal_le value bound) /\
  (forall upper : q1191709_ennreal,
      (forall value : q1191709_ennreal,
        values value -> q1191709_ennreal_le value upper) ->
      q1191709_ennreal_le bound upper).

Definition q1191709_ennreal_series_sum
    (u : nat -> q1191709_ennreal)
    (sum : q1191709_ennreal) : Prop :=
  q1191709_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1191709_ennreal_eq value
          (q1191709_ennreal_partial_sum u n))
    sum.

Record q1191709_measurable_space (A : Type) : Type := {
  q1191709_measurable : q1191709_set A -> Prop;
  q1191709_measurable_extensional :
    forall E F : q1191709_set A,
      q1191709_same_set E F ->
      (q1191709_measurable E <-> q1191709_measurable F);
  q1191709_measurable_empty :
    q1191709_measurable q1191709_empty;
  q1191709_measurable_complement :
    forall E : q1191709_set A,
      q1191709_measurable E ->
      q1191709_measurable (q1191709_complement E);
  q1191709_measurable_countable_union :
    forall E : nat -> q1191709_set A,
      (forall n : nat, q1191709_measurable (E n)) ->
      q1191709_measurable (q1191709_countable_union E)
}.

Arguments q1191709_measurable {A} _ _.

Record q1191709_measure (A : Type)
    (m : q1191709_measurable_space A) : Type := {
  q1191709_measure_value : q1191709_set A -> q1191709_ennreal;
  q1191709_measure_extensional :
    forall E F : q1191709_set A,
      q1191709_same_set E F ->
      q1191709_ennreal_eq
        (q1191709_measure_value E)
        (q1191709_measure_value F);
  q1191709_measure_empty :
    q1191709_ennreal_eq
      (q1191709_measure_value q1191709_empty)
      q1191709_ennreal_zero;
  q1191709_measure_monotone :
    forall E F : q1191709_set A,
      q1191709_subset E F ->
      q1191709_ennreal_le
        (q1191709_measure_value E)
        (q1191709_measure_value F);
  q1191709_measure_trim :
    forall E : q1191709_set A,
      exists F : q1191709_set A,
        q1191709_measurable m F /\
        q1191709_subset E F /\
        q1191709_ennreal_eq
          (q1191709_measure_value F)
          (q1191709_measure_value E);
  q1191709_measure_countable_additive :
    forall E : nat -> q1191709_set A,
      (forall n : nat, q1191709_measurable m (E n)) ->
      q1191709_pairwise_disjoint E ->
      q1191709_ennreal_series_sum
        (fun n => q1191709_measure_value (E n))
        (q1191709_measure_value (q1191709_countable_union E))
}.

Arguments q1191709_measure_value {A m} _ _.

Definition q1191709_almost_everywhere {A : Type}
    {m : q1191709_measurable_space A}
    (mu : q1191709_measure m)
    (P : A -> Prop) : Prop :=
  exists null_set : q1191709_set A,
    q1191709_measurable m null_set /\
    q1191709_ennreal_eq
      (q1191709_measure_value mu null_set)
      q1191709_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q1191709_countable_sup_index (I : Type) : Type := {
  q1191709_index_le : I -> I -> Prop;
  q1191709_index_le_refl :
    forall i : I, q1191709_index_le i i;
  q1191709_index_le_trans :
    forall i j k : I,
      q1191709_index_le i j ->
      q1191709_index_le j k ->
      q1191709_index_le i k;
  q1191709_index_le_antisymmetric :
    forall i j : I,
      q1191709_index_le i j ->
      q1191709_index_le j i ->
      i = j;
  q1191709_index_sup : I -> I -> I;
  q1191709_index_le_sup_left :
    forall i j : I,
      q1191709_index_le i (q1191709_index_sup i j);
  q1191709_index_le_sup_right :
    forall i j : I,
      q1191709_index_le j (q1191709_index_sup i j);
  q1191709_index_sup_le :
    forall i j k : I,
      q1191709_index_le i k ->
      q1191709_index_le j k ->
      q1191709_index_le (q1191709_index_sup i j) k;
  q1191709_index_inhabitant : I;
  q1191709_index_encode : I -> nat;
  q1191709_index_encode_injective :
    forall i j : I,
      q1191709_index_encode i = q1191709_index_encode j ->
      i = j
}.

Arguments q1191709_index_le {I} _ _ _.

Record q1191709_pseudo_emetric_space (B : Type) : Type := {
  q1191709_edist : B -> B -> q1191709_ennreal;
  q1191709_edist_self :
    forall x : B,
      q1191709_ennreal_eq
        (q1191709_edist x x) q1191709_ennreal_zero;
  q1191709_edist_comm :
    forall x y : B,
      q1191709_ennreal_eq
        (q1191709_edist x y) (q1191709_edist y x);
  q1191709_edist_triangle :
    forall x y z : B,
      q1191709_ennreal_le
        (q1191709_edist x z)
        (q1191709_ennreal_add
          (q1191709_edist x y) (q1191709_edist y z))
}.

Arguments q1191709_edist {B} _ _ _.

Definition q1191709_nat_sequence_converges {B : Type}
    (E : q1191709_pseudo_emetric_space B)
    (u : nat -> B) (limit : B) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1191709_ennreal_lt_real
          (q1191709_edist E (u n) limit) epsilon.

Definition q1191709_indexed_converges {I B : Type}
    (J : q1191709_countable_sup_index I)
    (E : q1191709_pseudo_emetric_space B)
    (u : I -> B) (limit : B) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : I,
      forall n : I,
        q1191709_index_le J N n ->
        q1191709_ennreal_lt_real
          (q1191709_edist E (u n) limit) epsilon.

Definition q1191709_measurable_simple {A B : Type}
    (m : q1191709_measurable_space A)
    (simple : A -> B) : Prop :=
  exists (k : nat) (code : A -> nat),
    (forall x : A, (code x < k)%nat) /\
    (forall x y : A,
      code x = code y <-> simple x = simple y) /\
    forall i : nat,
      (i < k)%nat ->
      q1191709_measurable m (fun x => code x = i).

Definition q1191709_strongly_measurable {A B : Type}
    (m : q1191709_measurable_space A)
    (E : q1191709_pseudo_emetric_space B)
    (f : A -> B) : Prop :=
  exists approximants : nat -> A -> B,
    (forall n : nat,
      q1191709_measurable_simple m (approximants n)) /\
    forall x : A,
      q1191709_nat_sequence_converges E
        (fun n => approximants n x) (f x).

Definition q1191709_tendsto_uniformly_on {I A B : Type}
    (J : q1191709_countable_sup_index I)
    (E : q1191709_pseudo_emetric_space B)
    (f : I -> A -> B) (g : A -> B)
    (s : q1191709_set A) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : I,
      forall (n : I) (x : A),
        q1191709_index_le J N n ->
        s x ->
        q1191709_ennreal_lt_real
          (q1191709_edist E (f n x) (g x)) epsilon.

Theorem tendstoUniformlyOn_of_ae_tendsto :
  forall (Alpha Beta I : Type)
         (m : q1191709_measurable_space Alpha)
         (mu : q1191709_measure m)
         (J : q1191709_countable_sup_index I)
         (E : q1191709_pseudo_emetric_space Beta)
         (f : I -> Alpha -> Beta)
         (g : Alpha -> Beta)
         (s : q1191709_set Alpha)
         (epsilon : R),
    (forall n : I,
      q1191709_strongly_measurable m E (f n)) ->
    q1191709_strongly_measurable m E g ->
    q1191709_measurable m s ->
    ~ q1191709_ennreal_eq
        (q1191709_measure_value mu s)
        q1191709_ennreal_infinity ->
    q1191709_almost_everywhere mu
      (fun x =>
        s x ->
        q1191709_indexed_converges J E
          (fun n => f n x) (g x)) ->
    0 < epsilon ->
    exists t : q1191709_set Alpha,
      q1191709_subset t s /\
      q1191709_measurable m t /\
      q1191709_ennreal_le_real
        (q1191709_measure_value mu t) epsilon /\
      q1191709_tendsto_uniformly_on J E f g
        (q1191709_difference s t).
Admitted.
