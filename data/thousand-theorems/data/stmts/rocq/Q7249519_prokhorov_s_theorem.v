(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7249519
  (thousand-theorems__rocq__Q7249519), "Prokhorov's theorem": finite Borel
  measures with uniformly bounded mass and uniformly vanishing mass outside
  compact sets form a compact set in the weak topology, assuming normality of
  the space or monotonicity of the compact sets. This file contains no proof.
*)

From Stdlib Require Import Reals List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q7249519_set (A : Type) : Type := A -> Prop.

Definition q7249519_empty {A : Type} : q7249519_set A :=
  fun _ => False.

Definition q7249519_full {A : Type} : q7249519_set A :=
  fun _ => True.

Definition q7249519_complement {A : Type}
    (S : q7249519_set A) : q7249519_set A :=
  fun x => ~ S x.

Definition q7249519_intersection {A : Type}
    (S T : q7249519_set A) : q7249519_set A :=
  fun x => S x /\ T x.

Definition q7249519_countable_union {A : Type}
    (S : nat -> q7249519_set A) : q7249519_set A :=
  fun x => exists n : nat, S n x.

Definition q7249519_arbitrary_union {A : Type}
    (F : q7249519_set (q7249519_set A)) : q7249519_set A :=
  fun x => exists S : q7249519_set A, F S /\ S x.

Definition q7249519_same_set {A : Type}
    (S T : q7249519_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q7249519_subset {A : Type}
    (S T : q7249519_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q7249519_disjoint {A : Type}
    (S T : q7249519_set A) : Prop :=
  forall x : A, ~ (S x /\ T x).

Definition q7249519_pairwise_disjoint {A : Type}
    (S : nat -> q7249519_set A) : Prop :=
  forall i j : nat, i <> j ->
    q7249519_disjoint (S i) (S j).

Record q7249519_topological_space (E : Type) : Type := {
  q7249519_is_open : q7249519_set E -> Prop;
  q7249519_open_extensional :
    forall U V : q7249519_set E,
      q7249519_same_set U V ->
      (q7249519_is_open U <-> q7249519_is_open V);
  q7249519_open_full :
    q7249519_is_open q7249519_full;
  q7249519_open_intersection :
    forall U V : q7249519_set E,
      q7249519_is_open U ->
      q7249519_is_open V ->
      q7249519_is_open (q7249519_intersection U V);
  q7249519_open_arbitrary_union :
    forall F : q7249519_set (q7249519_set E),
      (forall U : q7249519_set E, F U -> q7249519_is_open U) ->
      q7249519_is_open (q7249519_arbitrary_union F)
}.

Arguments q7249519_is_open {E} _ _.

Definition q7249519_is_closed {E : Type}
    (T : q7249519_topological_space E)
    (S : q7249519_set E) : Prop :=
  q7249519_is_open T (q7249519_complement S).

Definition q7249519_t2_space {E : Type}
    (T : q7249519_topological_space E) : Prop :=
  forall x y : E,
    x <> y ->
    exists U V : q7249519_set E,
      q7249519_is_open T U /\
      q7249519_is_open T V /\
      U x /\ V y /\
      q7249519_disjoint U V.

Definition q7249519_normal_space {E : Type}
    (T : q7249519_topological_space E) : Prop :=
  forall A B : q7249519_set E,
    q7249519_is_closed T A ->
    q7249519_is_closed T B ->
    q7249519_disjoint A B ->
    exists U V : q7249519_set E,
      q7249519_is_open T U /\
      q7249519_is_open T V /\
      q7249519_subset A U /\
      q7249519_subset B V /\
      q7249519_disjoint U V.

Record q7249519_measurable_space (E : Type) : Type := {
  q7249519_measurable : q7249519_set E -> Prop;
  q7249519_measurable_extensional :
    forall A B : q7249519_set E,
      q7249519_same_set A B ->
      (q7249519_measurable A <-> q7249519_measurable B);
  q7249519_measurable_empty :
    q7249519_measurable q7249519_empty;
  q7249519_measurable_complement :
    forall A : q7249519_set E,
      q7249519_measurable A ->
      q7249519_measurable (q7249519_complement A);
  q7249519_measurable_countable_union :
    forall A : nat -> q7249519_set E,
      (forall n : nat, q7249519_measurable (A n)) ->
      q7249519_measurable (q7249519_countable_union A)
}.

Arguments q7249519_measurable {E} _ _.

Definition q7249519_sigma_class {E : Type}
    (C : q7249519_set (q7249519_set E)) : Prop :=
  C q7249519_empty /\
  (forall A : q7249519_set E,
    C A -> C (q7249519_complement A)) /\
  (forall A : nat -> q7249519_set E,
    (forall n : nat, C (A n)) ->
    C (q7249519_countable_union A)).

Definition q7249519_borel_set {E : Type}
    (T : q7249519_topological_space E)
    (A : q7249519_set E) : Prop :=
  forall C : q7249519_set (q7249519_set E),
    q7249519_sigma_class C ->
    (forall U : q7249519_set E,
      q7249519_is_open T U -> C U) ->
    C A.

Definition q7249519_borel_space {E : Type}
    (T : q7249519_topological_space E)
    (M : q7249519_measurable_space E) : Prop :=
  forall A : q7249519_set E,
    q7249519_measurable M A <->
    q7249519_borel_set T A.

Definition q7249519_is_compact {A : Type}
    (is_open : q7249519_set A -> Prop)
    (K : q7249519_set A) : Prop :=
  forall cover : q7249519_set (q7249519_set A),
    (forall U : q7249519_set A, cover U -> is_open U) ->
    (forall x : A,
      K x ->
      exists U : q7249519_set A, cover U /\ U x) ->
    exists finite_cover : list (q7249519_set A),
      Forall cover finite_cover /\
      forall x : A,
        K x ->
        exists U : q7249519_set A,
          In U finite_cover /\ U x.

Record q7249519_nnreal : Type := {
  q7249519_nnreal_value : R;
  q7249519_nnreal_nonnegative :
    0 <= q7249519_nnreal_value
}.

Definition q7249519_tends_to_zero
    (u : nat -> q7249519_nnreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q7249519_nnreal_value (u n) < epsilon.

Fixpoint q7249519_sum_first
    (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S k => q7249519_sum_first k f + f k
  end.

Definition q7249519_sequence_converges
    (f : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (f n - limit) < epsilon.

Definition q7249519_series_sum
    (f : nat -> R) (sum : R) : Prop :=
  q7249519_sequence_converges
    (fun n => q7249519_sum_first n f) sum.

Definition q7249519_infimum
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> bound <= value) /\
  (forall lower : R,
    (forall value : R, values value -> lower <= value) ->
    lower <= bound).

Record q7249519_finite_measure
    (E : Type) (M : q7249519_measurable_space E) : Type := {
  q7249519_measure : q7249519_set E -> R;
  q7249519_measure_extensional :
    forall A B : q7249519_set E,
      q7249519_same_set A B ->
      q7249519_measure A = q7249519_measure B;
  q7249519_measure_nonnegative :
    forall A : q7249519_set E,
      0 <= q7249519_measure A;
  q7249519_measure_empty :
    q7249519_measure q7249519_empty = 0;
  q7249519_measure_monotone :
    forall A B : q7249519_set E,
      q7249519_subset A B ->
      q7249519_measure A <= q7249519_measure B;
  q7249519_measure_trimmed :
    forall A : q7249519_set E,
      q7249519_infimum
        (fun value : R =>
          exists B : q7249519_set E,
            q7249519_measurable M B /\
            q7249519_subset A B /\
            value = q7249519_measure B)
        (q7249519_measure A);
  q7249519_measure_countable_additive :
    forall A : nat -> q7249519_set E,
      (forall n : nat, q7249519_measurable M (A n)) ->
      q7249519_pairwise_disjoint A ->
      q7249519_series_sum
        (fun n => q7249519_measure (A n))
        (q7249519_measure (q7249519_countable_union A))
}.

Arguments q7249519_finite_measure E M : clear implicits.
Arguments q7249519_measure {E M} _ _.

Definition q7249519_mass {E : Type}
    {M : q7249519_measurable_space E}
    (mu : q7249519_finite_measure E M) : R :=
  q7249519_measure mu q7249519_full.

Definition q7249519_real_open
    (U : q7249519_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q7249519_continuous {E : Type}
    (T : q7249519_topological_space E)
    (f : E -> R) : Prop :=
  forall U : q7249519_set R,
    q7249519_real_open U ->
    q7249519_is_open T
      (fun x : E => U (f x)).

Definition q7249519_bounded
    {E : Type} (f : E -> R) : Prop :=
  exists bound : R,
    0 <= bound /\
    forall x : E, Rabs (f x) <= bound.

Definition q7249519_bounded_continuous {E : Type}
    (T : q7249519_topological_space E)
    (f : E -> R) : Prop :=
  q7249519_continuous T f /\
  q7249519_bounded f.

Definition q7249519_finite_partition {E : Type}
    (M : q7249519_measurable_space E)
    (k : nat) (cells : nat -> q7249519_set E) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat ->
    q7249519_measurable M (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q7249519_disjoint (cells i) (cells j)) /\
  (forall x : E,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q7249519_simple_integral_below {E : Type}
    {M : q7249519_measurable_space E}
    (mu : q7249519_finite_measure E M)
    (f : E -> R) (value : R) : Prop :=
  exists (k : nat) (coefficients : nat -> R)
         (cells : nat -> q7249519_set E),
    q7249519_finite_partition M k cells /\
    (forall i : nat,
      (i < k)%nat -> 0 <= coefficients i) /\
    (forall (x : E) (i : nat),
      (i < k)%nat ->
      cells i x ->
      coefficients i <= f x) /\
    value =
      q7249519_sum_first k
        (fun i =>
          coefficients i * q7249519_measure mu (cells i)).

Definition q7249519_supremum
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> value <= bound) /\
  (forall upper : R,
    (forall value : R, values value -> value <= upper) ->
    bound <= upper).

Definition q7249519_nonnegative_integral {E : Type}
    {M : q7249519_measurable_space E}
    (mu : q7249519_finite_measure E M)
    (f : E -> R) (value : R) : Prop :=
  q7249519_supremum
    (q7249519_simple_integral_below mu f) value.

Definition q7249519_positive_part (x : R) : R :=
  Rmax x 0.

Definition q7249519_negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition q7249519_integral {E : Type}
    {M : q7249519_measurable_space E}
    (mu : q7249519_finite_measure E M)
    (f : E -> R) (value : R) : Prop :=
  exists positive_integral negative_integral : R,
    q7249519_nonnegative_integral mu
      (fun x => q7249519_positive_part (f x))
      positive_integral /\
    q7249519_nonnegative_integral mu
      (fun x => q7249519_negative_part (f x))
      negative_integral /\
    value = positive_integral - negative_integral.

Definition q7249519_weak_basic_neighborhood {E : Type}
    (T : q7249519_topological_space E)
    {M : q7249519_measurable_space E}
    (center : q7249519_finite_measure E M)
    (tests : list (E -> R)) (epsilon : R)
    (mu : q7249519_finite_measure E M) : Prop :=
  0 < epsilon /\
  Forall (q7249519_bounded_continuous T) tests /\
  forall f : E -> R,
    In f tests ->
    exists center_value mu_value : R,
      q7249519_integral center f center_value /\
      q7249519_integral mu f mu_value /\
      Rabs (mu_value - center_value) < epsilon.

Definition q7249519_weak_is_open {E : Type}
    (T : q7249519_topological_space E)
    (M : q7249519_measurable_space E)
    (U : q7249519_set (q7249519_finite_measure E M)) : Prop :=
  forall mu : q7249519_finite_measure E M,
    U mu ->
    exists (tests : list (E -> R)) (epsilon : R),
      q7249519_weak_basic_neighborhood
        T mu tests epsilon mu /\
      forall nu : q7249519_finite_measure E M,
        q7249519_weak_basic_neighborhood
          T mu tests epsilon nu ->
        U nu.

Definition q7249519_monotone_sets {E : Type}
    (K : nat -> q7249519_set E) : Prop :=
  forall m n : nat,
    (m <= n)%nat ->
    q7249519_subset (K m) (K n).

Theorem q7249519_prokhorov :
  forall (E : Type)
         (T : q7249519_topological_space E)
         (M : q7249519_measurable_space E)
         (u : nat -> q7249519_nnreal)
         (K : nat -> q7249519_set E)
         (C : q7249519_nnreal),
    q7249519_t2_space T ->
    q7249519_borel_space T M ->
    q7249519_tends_to_zero u ->
    (forall n : nat,
      q7249519_is_compact
        (q7249519_is_open T) (K n)) ->
    (q7249519_normal_space T \/
     q7249519_monotone_sets K) ->
    q7249519_is_compact
      (@q7249519_weak_is_open E T M)
      (fun mu : q7249519_finite_measure E M =>
        q7249519_mass mu <= q7249519_nnreal_value C /\
        forall n : nat,
          q7249519_measure mu
              (q7249519_complement (K n))
            <= q7249519_nnreal_value (u n)).
Admitted.
