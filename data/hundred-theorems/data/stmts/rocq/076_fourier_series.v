(*
  L2 convergence of Fourier series on [-pi, pi].

  The domain measure is explicitly complete and contains every Borel set, so
  the function class is Lebesgue measurable rather than merely Borel
  measurable.  This matches the source theorem's square-integrable class.
*)

From Stdlib Require Import Reals Rtrigo List.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition subset_set {A : Type} (E F : set A) : Prop :=
  forall x, E x -> F x.

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x, E x <-> F x.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition set_intersection {A : Type} (E F : set A) : set A :=
  fun x => E x /\ F x.

Definition symmetric_difference {A : Type} (E F : set A) : set A :=
  fun x => (E x /\ ~ F x) \/ (F x /\ ~ E x).

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n, E n x.

Definition preimage {A B : Type} (f : A -> B) (E : set B) : set A :=
  fun x => E (f x).

Definition disjoint_sets {A : Type} (E F : set A) : Prop :=
  forall x, ~ (E x /\ F x).

Definition pairwise_disjoint {A : Type} (E : nat -> set A) : Prop :=
  forall i j, i <> j -> disjoint_sets (E i) (E j).

Fixpoint partial_sum (u : nat -> R) (n : nat) : R :=
  match n with
  | O => u O
  | S k => partial_sum u k + u (S k)
  end.

Definition sequence_converges (u : nat -> R) (limit : R) : Prop :=
  forall eps,
    0 < eps ->
    exists N,
      forall n, (N <= n)%nat -> Rabs (u n - limit) < eps.

Definition series_sum (u : nat -> R) (sum : R) : Prop :=
  sequence_converges (partial_sum u) sum.

Definition sigma_class {A : Type} (C : set (set A)) : Prop :=
  C empty_set /\
  (forall E, C E -> C (set_complement E)) /\
  (forall E : nat -> set A,
      (forall n, C (E n)) ->
      C (countable_union E)).

Definition open_real_set (U : set R) : Prop :=
  forall x,
    U x ->
    exists eps,
      0 < eps /\
      forall y, Rabs (y - x) < eps -> U y.

Definition borel_set (E : set R) : Prop :=
  forall C : set (set R),
    sigma_class C ->
    (forall U, open_real_set U -> C U) ->
    C E.

Record complete_real_measure := {
  crm_measurable : set (set R);
  crm_measure : set R -> R;
  crm_sigma_algebra : sigma_class crm_measurable;
  crm_contains_borel :
    forall E, borel_set E -> crm_measurable E;
  crm_measure_extensional :
    forall E F,
      crm_measurable E ->
      crm_measurable F ->
      same_set E F ->
      crm_measure E = crm_measure F;
  crm_measure_nonnegative :
    forall E, crm_measurable E -> 0 <= crm_measure E;
  crm_measure_empty :
    crm_measure empty_set = 0;
  crm_measure_countable_additive :
    forall E : nat -> set R,
      (forall n, crm_measurable (E n)) ->
      pairwise_disjoint E ->
      series_sum
        (fun n => crm_measure (E n))
        (crm_measure (countable_union E));
  crm_complete :
    forall null_set E,
      crm_measurable null_set ->
      crm_measure null_set = 0 ->
      subset_set E null_set ->
      crm_measurable E /\ crm_measure E = 0
}.

Definition is_borel_completion (mu : complete_real_measure) : Prop :=
  (forall E,
      crm_measurable mu E ->
      exists B N,
        borel_set B /\
        borel_set N /\
        crm_measure mu N = 0 /\
        subset_set (symmetric_difference E B) N) /\
  (forall E B N,
      borel_set B ->
      borel_set N ->
      crm_measure mu N = 0 ->
      subset_set (symmetric_difference E B) N ->
      crm_measurable mu E /\ crm_measure mu E = crm_measure mu B).

Definition standard_interval : set R :=
  fun x => - PI <= x <= PI.

Definition left_open_interval (a b : R) : set R :=
  fun x => a < x <= b.

Definition is_standard_interval_lebesgue_measure
    (mu : complete_real_measure) : Prop :=
  crm_measurable mu standard_interval /\
  is_borel_completion mu /\
  (forall E,
      crm_measurable mu E ->
      crm_measure mu E =
      crm_measure mu (set_intersection E standard_interval)) /\
  (forall a b,
      - PI <= a ->
      a <= b ->
      b <= PI ->
      crm_measure mu (left_open_interval a b) = b - a) /\
  crm_measure mu standard_interval = 2 * PI.

Definition lebesgue_measurable_on
    (mu : complete_real_measure) (D : set R) (f : R -> R) : Prop :=
  crm_measurable mu D /\
  forall B,
    borel_set B ->
    crm_measurable mu (set_intersection D (preimage f B)).

Definition finite_partition_on
    (mu : complete_real_measure)
    (D : set R) (k : nat) (cells : nat -> set R) : Prop :=
  (forall i, (i <= k)%nat -> crm_measurable mu (cells i)) /\
  (forall i,
      (i <= k)%nat ->
      forall x, cells i x -> D x) /\
  (forall i j,
      (i <= k)%nat ->
      (j <= k)%nat ->
      i <> j ->
      disjoint_sets (cells i) (cells j)) /\
  (forall x,
      D x ->
      exists i, (i <= k)%nat /\ cells i x).

Fixpoint finite_sum (k : nat) (f : nat -> R) : R :=
  match k with
  | O => f O
  | S n => finite_sum n f + f (S n)
  end.

Definition simple_integral_below_on
    (mu : complete_real_measure) (D : set R)
    (f : R -> R) (value : R) : Prop :=
  exists (k : nat) (coefficients : nat -> R) (cells : nat -> set R),
    finite_partition_on mu D k cells /\
    (forall i, (i <= k)%nat -> 0 <= coefficients i) /\
    (forall x i,
        (i <= k)%nat ->
        cells i x ->
        coefficients i <= f x) /\
    value =
      finite_sum k
        (fun i => coefficients i * crm_measure mu (cells i)).

Definition least_upper_bound (values : R -> Prop) (bound : R) : Prop :=
  (forall value, values value -> value <= bound) /\
  (forall upper,
      (forall value, values value -> value <= upper) ->
      bound <= upper).

Definition nonnegative_lebesgue_integral_on
    (mu : complete_real_measure) (D : set R)
    (f : R -> R) (value : R) : Prop :=
  least_upper_bound
    (simple_integral_below_on mu D f)
    value.

Definition positive_part (x : R) : R :=
  Rmax x 0.

Definition negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition has_finite_lebesgue_integral_on
    (mu : complete_real_measure) (D : set R)
    (f : R -> R) (value : R) : Prop :=
  lebesgue_measurable_on mu D f /\
  exists positive_integral negative_integral,
    nonnegative_lebesgue_integral_on mu D
      (fun x => positive_part (f x)) positive_integral /\
    nonnegative_lebesgue_integral_on mu D
      (fun x => negative_part (f x)) negative_integral /\
    value = positive_integral - negative_integral.

Definition has_interval_integral
    (mu : complete_real_measure) (f : R -> R) (value : R) : Prop :=
  has_finite_lebesgue_integral_on mu standard_interval f value.

Definition square_integrable_on_standard_interval
    (mu : complete_real_measure) (f : R -> R) : Prop :=
  lebesgue_measurable_on mu standard_interval f /\
  exists value,
    has_interval_integral mu (fun x => (f x) ^ 2) value.

Definition trigonometric_system (n : nat) (x : R) : R :=
  match n with
  | O => 1 / sqrt (2 * PI)
  | S _ =>
      if Nat.odd n
      then sin (INR (Nat.div n 2 + 1) * x) / sqrt PI
      else cos (INR (Nat.div n 2) * x) / sqrt PI
  end.

Definition has_fourier_coefficient
    (mu : complete_real_measure) (f : R -> R)
    (n : nat) (coefficient : R) : Prop :=
  has_interval_integral mu
    (fun x => trigonometric_system n x * f x)
    coefficient.

Definition fourier_partial_sum
    (coefficients : nat -> R) (n : nat) (x : R) : R :=
  finite_sum n
    (fun k => coefficients k * trigonometric_system k x).

Definition has_l2_norm
    (mu : complete_real_measure) (f : R -> R) (norm : R) : Prop :=
  exists square_integral,
    has_interval_integral mu (fun x => (f x) ^ 2) square_integral /\
    norm = sqrt square_integral.

Theorem fourier_series_l2 :
  forall mu,
    is_standard_interval_lebesgue_measure mu ->
    forall f,
      square_integrable_on_standard_interval mu f ->
      exists coefficients : nat -> R,
        (forall k,
            has_fourier_coefficient mu f k (coefficients k)) /\
        exists errors : nat -> R,
          (forall n,
              has_l2_norm mu
                (fun x => f x - fourier_partial_sum coefficients n x)
                (errors n)) /\
          sequence_converges errors 0.
Proof.
Admitted.
