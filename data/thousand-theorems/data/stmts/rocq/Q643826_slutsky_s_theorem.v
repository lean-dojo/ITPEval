(*
  Statement-only formalization of Thousand Theorems corpus artifact Q643826
  (thousand-theorems__rocq__Q643826), "Slutsky's theorem": a continuous
  function of random variables converging respectively in distribution and
  in measure to a constant converges in distribution to the corresponding
  continuous function of the limits. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q643826_event (A : Type) : Type := A -> Prop.

Definition q643826_empty {A : Type} : q643826_event A :=
  fun _ => False.

Definition q643826_full {A : Type} : q643826_event A :=
  fun _ => True.

Definition q643826_complement {A : Type}
    (U : q643826_event A) : q643826_event A :=
  fun x => ~ U x.

Definition q643826_countable_union {A : Type}
    (U : nat -> q643826_event A) : q643826_event A :=
  fun x => exists n : nat, U n x.

Definition q643826_same_event {A : Type}
    (U V : q643826_event A) : Prop :=
  forall x : A, U x <-> V x.

Definition q643826_subset {A : Type}
    (U V : q643826_event A) : Prop :=
  forall x : A, U x -> V x.

Definition q643826_disjoint {A : Type}
    (U V : q643826_event A) : Prop :=
  forall x : A, ~ (U x /\ V x).

Definition q643826_pairwise_disjoint {A : Type}
    (U : nat -> q643826_event A) : Prop :=
  forall i j : nat,
    i <> j -> q643826_disjoint (U i) (U j).

Record q643826_sigma_algebra (A : Type) : Type := {
  q643826_measurable : q643826_event A -> Prop;
  q643826_measurable_extensional :
    forall U V : q643826_event A,
      q643826_same_event U V ->
      (q643826_measurable U <-> q643826_measurable V);
  q643826_measurable_empty :
    q643826_measurable q643826_empty;
  q643826_measurable_complement :
    forall U : q643826_event A,
      q643826_measurable U ->
      q643826_measurable (q643826_complement U);
  q643826_measurable_countable_union :
    forall U : nat -> q643826_event A,
      (forall n : nat, q643826_measurable (U n)) ->
      q643826_measurable (q643826_countable_union U)
}.

Arguments q643826_measurable {A} _ _.

Record q643826_topological_space (A : Type) : Type := {
  q643826_is_open : q643826_event A -> Prop;
  q643826_open_extensional :
    forall U V : q643826_event A,
      q643826_same_event U V ->
      (q643826_is_open U <-> q643826_is_open V);
  q643826_open_empty :
    q643826_is_open q643826_empty;
  q643826_open_full :
    q643826_is_open q643826_full;
  q643826_open_intersection :
    forall U V : q643826_event A,
      q643826_is_open U ->
      q643826_is_open V ->
      q643826_is_open (fun x => U x /\ V x);
  q643826_open_union :
    forall family : q643826_event A -> Prop,
      (forall U : q643826_event A,
        family U -> q643826_is_open U) ->
      q643826_is_open
        (fun x =>
          exists U : q643826_event A,
            family U /\ U x)
}.

Arguments q643826_is_open {A} _ _.

Inductive q643826_borel {A : Type}
    (T : q643826_topological_space A)
    : q643826_event A -> Prop :=
| q643826_borel_open :
    forall U : q643826_event A,
      q643826_is_open T U ->
      q643826_borel T U
| q643826_borel_extensional :
    forall U V : q643826_event A,
      q643826_borel T U ->
      q643826_same_event U V ->
      q643826_borel T V
| q643826_borel_complement :
    forall U : q643826_event A,
      q643826_borel T U ->
      q643826_borel T (q643826_complement U)
| q643826_borel_countable_union :
    forall U : nat -> q643826_event A,
      (forall n : nat, q643826_borel T (U n)) ->
      q643826_borel T (q643826_countable_union U).

Definition q643826_is_borel_space {A : Type}
    (T : q643826_topological_space A)
    (M : q643826_sigma_algebra A) : Prop :=
  forall U : q643826_event A,
    q643826_measurable M U <-> q643826_borel T U.

Definition q643826_second_countable {A : Type}
    (T : q643826_topological_space A) : Prop :=
  exists basis : nat -> q643826_event A,
    (forall n : nat, q643826_is_open T (basis n)) /\
    forall (U : q643826_event A) (x : A),
      q643826_is_open T U ->
      U x ->
      exists n : nat,
        basis n x /\ q643826_subset (basis n) U.

Definition q643826_continuous {A B : Type}
    (TA : q643826_topological_space A)
    (TB : q643826_topological_space B)
    (f : A -> B) : Prop :=
  forall U : q643826_event B,
    q643826_is_open TB U ->
    q643826_is_open TA (fun x => U (f x)).

Definition q643826_product_open {A B : Type}
    (TA : q643826_topological_space A)
    (TB : q643826_topological_space B)
    (W : q643826_event (A * B)) : Prop :=
  forall (x : A) (y : B),
    W (x, y) ->
    exists (U : q643826_event A) (V : q643826_event B),
      q643826_is_open TA U /\
      q643826_is_open TB V /\
      U x /\ V y /\
      forall (a : A) (b : B), U a -> V b -> W (a, b).

Definition q643826_continuous_from_product {A B C : Type}
    (TA : q643826_topological_space A)
    (TB : q643826_topological_space B)
    (TC : q643826_topological_space C)
    (f : A * B -> C) : Prop :=
  forall U : q643826_event C,
    q643826_is_open TC U ->
    q643826_product_open TA TB (fun p => U (f p)).

Record q643826_seminormed_add_comm_group (A : Type) : Type := {
  q643826_zero : A;
  q643826_add : A -> A -> A;
  q643826_neg : A -> A;
  q643826_norm : A -> R;
  q643826_add_assoc :
    forall x y z : A,
      q643826_add x (q643826_add y z) =
      q643826_add (q643826_add x y) z;
  q643826_add_comm :
    forall x y : A,
      q643826_add x y = q643826_add y x;
  q643826_zero_add :
    forall x : A, q643826_add q643826_zero x = x;
  q643826_neg_add :
    forall x : A,
      q643826_add (q643826_neg x) x = q643826_zero;
  q643826_norm_nonnegative :
    forall x : A, 0 <= q643826_norm x;
  q643826_norm_zero :
    q643826_norm q643826_zero = 0;
  q643826_norm_neg :
    forall x : A,
      q643826_norm (q643826_neg x) = q643826_norm x;
  q643826_norm_add :
    forall x y : A,
      q643826_norm (q643826_add x y) <=
      q643826_norm x + q643826_norm y;
  q643826_topology : q643826_topological_space A;
  q643826_open_iff_norm :
    forall U : q643826_event A,
      q643826_is_open q643826_topology U <->
      forall x : A,
        U x ->
        exists epsilon : R,
          0 < epsilon /\
          forall y : A,
            q643826_norm
              (q643826_add y (q643826_neg x)) < epsilon ->
            U y
}.

Arguments q643826_zero {A} _.
Arguments q643826_add {A} _ _ _.
Arguments q643826_neg {A} _ _.
Arguments q643826_norm {A} _ _.
Arguments q643826_topology {A} _.

Definition q643826_sub {A : Type}
    (V : q643826_seminormed_add_comm_group A)
    (x y : A) : A :=
  q643826_add V x (q643826_neg V y).

Definition q643826_real_open
    (U : q643826_event R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon -> U y.

Inductive q643826_real_borel : q643826_event R -> Prop :=
| q643826_real_borel_open :
    forall U : q643826_event R,
      q643826_real_open U ->
      q643826_real_borel U
| q643826_real_borel_extensional :
    forall U V : q643826_event R,
      q643826_real_borel U ->
      q643826_same_event U V ->
      q643826_real_borel V
| q643826_real_borel_complement :
    forall U : q643826_event R,
      q643826_real_borel U ->
      q643826_real_borel (q643826_complement U)
| q643826_real_borel_countable_union :
    forall U : nat -> q643826_event R,
      (forall n : nat, q643826_real_borel (U n)) ->
      q643826_real_borel (q643826_countable_union U).

Definition q643826_continuous_to_real {A : Type}
    (T : q643826_topological_space A)
    (f : A -> R) : Prop :=
  forall U : q643826_event R,
    q643826_real_open U ->
    q643826_is_open T (fun x => U (f x)).

Definition q643826_measurable_function {A B : Type}
    (MA : q643826_sigma_algebra A)
    (MB : q643826_sigma_algebra B)
    (f : A -> B) : Prop :=
  forall U : q643826_event B,
    q643826_measurable MB U ->
    q643826_measurable MA (fun x => U (f x)).

Definition q643826_measurable_real_function {A : Type}
    (MA : q643826_sigma_algebra A)
    (f : A -> R) : Prop :=
  forall U : q643826_event R,
    q643826_real_borel U ->
    q643826_measurable MA (fun x => U (f x)).

Fixpoint q643826_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q643826_partial_sum u k + u k
  end.

Definition q643826_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Record q643826_probability_mass
    (A : Type) (M : q643826_sigma_algebra A) : Type := {
  q643826_mass : q643826_event A -> R;
  q643826_mass_extensional :
    forall U V : q643826_event A,
      q643826_measurable M U ->
      q643826_measurable M V ->
      q643826_same_event U V ->
      q643826_mass U = q643826_mass V;
  q643826_mass_empty :
    q643826_mass q643826_empty = 0;
  q643826_mass_full :
    q643826_mass q643826_full = 1;
  q643826_mass_nonnegative :
    forall U : q643826_event A,
      q643826_measurable M U ->
      0 <= q643826_mass U;
  q643826_mass_countably_additive :
    forall U : nat -> q643826_event A,
      (forall n : nat, q643826_measurable M (U n)) ->
      q643826_pairwise_disjoint U ->
      q643826_real_sequence_converges
        (fun n =>
          q643826_partial_sum
            (fun k => q643826_mass (U k)) n)
        (q643826_mass (q643826_countable_union U))
}.

Arguments q643826_probability_mass A M : clear implicits.
Arguments q643826_mass {A M} _ _.

Definition q643826_almost_everywhere {A : Type}
    {M : q643826_sigma_algebra A}
    (mu : q643826_probability_mass A M)
    (P : A -> Prop) : Prop :=
  exists N : q643826_event A,
    q643826_measurable M N /\
    q643826_mass mu N = 0 /\
    forall x : A, ~ P x -> N x.

Definition q643826_ae_equal {A B : Type}
    {M : q643826_sigma_algebra A}
    (mu : q643826_probability_mass A M)
    (f g : A -> B) : Prop :=
  q643826_almost_everywhere mu (fun x => f x = g x).

Definition q643826_ae_measurable {A B : Type}
    (MA : q643826_sigma_algebra A)
    (MB : q643826_sigma_algebra B)
    (mu : q643826_probability_mass A MA)
    (f : A -> B) : Prop :=
  exists g : A -> B,
    q643826_measurable_function MA MB g /\
    q643826_ae_equal mu f g.

Arguments q643826_ae_measurable {A B} MA MB mu f.

Definition q643826_ae_measurable_real {A : Type}
    (MA : q643826_sigma_algebra A)
    (mu : q643826_probability_mass A MA)
    (f : A -> R) : Prop :=
  exists g : A -> R,
    q643826_measurable_real_function MA g /\
    q643826_ae_equal mu f g.

Arguments q643826_ae_measurable_real {A} MA mu f.

Definition q643826_bounded {A : Type}
    (f : A -> R) : Prop :=
  exists C : R,
    0 <= C /\ forall x : A, Rabs (f x) <= C.

Definition q643826_nonnegative {A : Type}
    (f : A -> R) : Prop :=
  forall x : A, 0 <= f x.

Definition q643826_increasing {A : Type}
    (f : nat -> A -> R) : Prop :=
  forall (n : nat) (x : A), f n x <= f (S n) x.

Definition q643826_is_indicator {A : Type}
    (U : q643826_event A)
    (f : A -> R) : Prop :=
  forall x : A,
    (U x /\ f x = 1) \/ (~ U x /\ f x = 0).

Record q643826_probability_measure
    (A : Type) (M : q643826_sigma_algebra A) : Type := {
  q643826_probability_mass_part :
    q643826_probability_mass A M;
  q643826_integral : (A -> R) -> R;
  q643826_integral_ae_extensional :
    forall f g : A -> R,
      q643826_ae_measurable_real M
        q643826_probability_mass_part f ->
      q643826_ae_measurable_real M
        q643826_probability_mass_part g ->
      q643826_bounded f ->
      q643826_bounded g ->
      q643826_ae_equal
        q643826_probability_mass_part f g ->
      q643826_integral f = q643826_integral g;
  q643826_integral_indicator :
    forall (U : q643826_event A) (f : A -> R),
      q643826_measurable M U ->
      q643826_is_indicator U f ->
      q643826_integral f =
      q643826_mass q643826_probability_mass_part U;
  q643826_integral_add :
    forall f g : A -> R,
      q643826_ae_measurable_real M
        q643826_probability_mass_part f ->
      q643826_ae_measurable_real M
        q643826_probability_mass_part g ->
      q643826_bounded f ->
      q643826_bounded g ->
      q643826_integral (fun x => f x + g x) =
      q643826_integral f + q643826_integral g;
  q643826_integral_scale :
    forall (c : R) (f : A -> R),
      q643826_ae_measurable_real M
        q643826_probability_mass_part f ->
      q643826_bounded f ->
      q643826_integral (fun x => c * f x) =
      c * q643826_integral f;
  q643826_integral_nonnegative :
    forall f : A -> R,
      q643826_ae_measurable_real M
        q643826_probability_mass_part f ->
      q643826_bounded f ->
      q643826_nonnegative f ->
      0 <= q643826_integral f;
  q643826_integral_monotone_convergence :
    forall (f : nat -> A -> R) (g : A -> R),
      (forall n : nat,
        q643826_ae_measurable_real M
          q643826_probability_mass_part (f n)) ->
      q643826_ae_measurable_real M
        q643826_probability_mass_part g ->
      (forall n : nat, q643826_bounded (f n)) ->
      q643826_bounded g ->
      (forall n : nat, q643826_nonnegative (f n)) ->
      q643826_increasing f ->
      (forall x : A,
        q643826_real_sequence_converges
          (fun n => f n x) (g x)) ->
      q643826_real_sequence_converges
        (fun n => q643826_integral (f n))
        (q643826_integral g)
}.

Arguments q643826_probability_measure A M : clear implicits.
Arguments q643826_probability_mass_part {A M} _.
Arguments q643826_integral {A M} _ _.

Record q643826_filter (I : Type) : Type := {
  q643826_eventually : (I -> Prop) -> Prop;
  q643826_eventually_true :
    q643826_eventually (fun _ => True);
  q643826_eventually_upward :
    forall P Q : I -> Prop,
      q643826_eventually P ->
      (forall i : I, P i -> Q i) ->
      q643826_eventually Q;
  q643826_eventually_intersection :
    forall P Q : I -> Prop,
      q643826_eventually P ->
      q643826_eventually Q ->
      q643826_eventually (fun i => P i /\ Q i)
}.

Arguments q643826_eventually {I} _ _.

Definition q643826_countably_generated {I : Type}
    (l : q643826_filter I) : Prop :=
  exists basis : nat -> q643826_event I,
    (forall n : nat, q643826_eventually l (basis n)) /\
    forall U : q643826_event I,
      q643826_eventually l U ->
      exists n : nat, q643826_subset (basis n) U.

Definition q643826_filter_tendsto_real {I : Type}
    (l : q643826_filter I)
    (u : I -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    q643826_eventually l
      (fun i => Rabs (u i - limit) < epsilon).

Definition q643826_tendsto_in_distribution
    {I Omega OmegaLimit E : Type}
    (TE : q643826_topological_space E)
    (ME : q643826_sigma_algebra E)
    (MOmega : q643826_sigma_algebra Omega)
    (MOLimit : q643826_sigma_algebra OmegaLimit)
    (mu : q643826_probability_measure Omega MOmega)
    (muLimit :
      q643826_probability_measure OmegaLimit MOLimit)
    (X : I -> Omega -> E)
    (l : q643826_filter I)
    (Z : OmegaLimit -> E) : Prop :=
  (forall i : I,
    q643826_ae_measurable
      MOmega ME
      (q643826_probability_mass_part mu)
      (X i)) /\
  q643826_ae_measurable
    MOLimit ME
    (q643826_probability_mass_part muLimit)
    Z /\
  forall h : E -> R,
    q643826_continuous_to_real TE h ->
    q643826_bounded h ->
    q643826_filter_tendsto_real l
      (fun i =>
        q643826_integral mu
          (fun omega => h (X i omega)))
      (q643826_integral muLimit
        (fun omega => h (Z omega))).

Arguments q643826_tendsto_in_distribution
  {I Omega OmegaLimit E}
  TE ME MOmega MOLimit mu muLimit X l Z.

Definition q643826_tendsto_in_measure_const
    {I Omega E : Type}
    (V : q643826_seminormed_add_comm_group E)
    (M : q643826_sigma_algebra Omega)
    (mu : q643826_probability_mass Omega M)
    (Y : I -> Omega -> E)
    (l : q643826_filter I)
    (c : E) : Prop :=
  forall epsilon delta : R,
    0 < epsilon ->
    0 < delta ->
    q643826_eventually l
      (fun i =>
        exists U : q643826_event Omega,
          q643826_measurable M U /\
          q643826_almost_everywhere mu
            (fun omega =>
              (epsilon <=
                q643826_norm V
                  (q643826_sub V (Y i omega) c))
              <-> U omega) /\
          q643826_mass mu U < delta).

Arguments q643826_tendsto_in_measure_const
  {I Omega E} V M mu Y l c.

Theorem q643826_slutsky_s_theorem :
  forall (I Omega OmegaLimit E E' F : Type)
         (VE : q643826_seminormed_add_comm_group E)
         (VE' : q643826_seminormed_add_comm_group E')
         (TF : q643826_topological_space F)
         (ME : q643826_sigma_algebra E)
         (ME' : q643826_sigma_algebra E')
         (MF : q643826_sigma_algebra F)
         (MOmega : q643826_sigma_algebra Omega)
         (MOLimit : q643826_sigma_algebra OmegaLimit)
         (mu : q643826_probability_measure Omega MOmega)
         (muLimit :
           q643826_probability_measure OmegaLimit MOLimit)
         (l : q643826_filter I)
         (X : I -> Omega -> E)
         (Y : I -> Omega -> E')
         (Z : OmegaLimit -> E)
         (c : E')
         (g : E * E' -> F),
    q643826_second_countable (q643826_topology VE) ->
    q643826_second_countable (q643826_topology VE') ->
    q643826_is_borel_space (q643826_topology VE) ME ->
    q643826_is_borel_space (q643826_topology VE') ME' ->
    q643826_is_borel_space TF MF ->
    q643826_countably_generated l ->
    q643826_continuous_from_product
      (q643826_topology VE) (q643826_topology VE') TF g ->
    q643826_tendsto_in_distribution
      (q643826_topology VE) ME
      MOmega MOLimit mu muLimit X l Z ->
    q643826_tendsto_in_measure_const
      VE' MOmega
      (q643826_probability_mass_part mu)
      Y l c ->
    (forall i : I,
      q643826_ae_measurable
        MOmega ME'
        (q643826_probability_mass_part mu)
        (Y i)) ->
    q643826_tendsto_in_distribution
      TF MF MOmega MOLimit mu muLimit
      (fun (i : I) (omega : Omega) =>
        g (X i omega, Y i omega))
      l
      (fun omega : OmegaLimit => g (Z omega, c)).
Admitted.
