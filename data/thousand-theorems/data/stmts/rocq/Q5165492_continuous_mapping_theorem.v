(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5165492
  (thousand-theorems__rocq__Q5165492), "Continuous mapping theorem":
  continuous composition preserves weak convergence of pushforward probability
  laws along an arbitrary filter for almost-everywhere measurable random
  variables on varying probability spaces. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q5165492_event (A : Type) : Type := A -> Prop.

Definition q5165492_empty {A : Type} : q5165492_event A :=
  fun _ => False.

Definition q5165492_full {A : Type} : q5165492_event A :=
  fun _ => True.

Definition q5165492_complement {A : Type}
    (E : q5165492_event A) : q5165492_event A :=
  fun x => ~ E x.

Definition q5165492_countable_union {A : Type}
    (E : nat -> q5165492_event A) : q5165492_event A :=
  fun x => exists n : nat, E n x.

Definition q5165492_same_event {A : Type}
    (E F : q5165492_event A) : Prop :=
  forall x : A, E x <-> F x.

Definition q5165492_disjoint {A : Type}
    (E F : q5165492_event A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q5165492_pairwise_disjoint {A : Type}
    (E : nat -> q5165492_event A) : Prop :=
  forall i j : nat,
    i <> j -> q5165492_disjoint (E i) (E j).

Record q5165492_sigma_algebra (A : Type) : Type := {
  q5165492_measurable : q5165492_event A -> Prop;
  q5165492_measurable_extensional :
    forall E F : q5165492_event A,
      q5165492_same_event E F ->
      (q5165492_measurable E <-> q5165492_measurable F);
  q5165492_measurable_empty :
    q5165492_measurable q5165492_empty;
  q5165492_measurable_complement :
    forall E : q5165492_event A,
      q5165492_measurable E ->
      q5165492_measurable (q5165492_complement E);
  q5165492_measurable_countable_union :
    forall E : nat -> q5165492_event A,
      (forall n : nat, q5165492_measurable (E n)) ->
      q5165492_measurable (q5165492_countable_union E)
}.

Arguments q5165492_measurable {A} _ _.

Record q5165492_topological_space (A : Type) : Type := {
  q5165492_is_open : q5165492_event A -> Prop;
  q5165492_open_extensional :
    forall U V : q5165492_event A,
      q5165492_same_event U V ->
      (q5165492_is_open U <-> q5165492_is_open V);
  q5165492_open_empty :
    q5165492_is_open q5165492_empty;
  q5165492_open_full :
    q5165492_is_open q5165492_full;
  q5165492_open_intersection :
    forall U V : q5165492_event A,
      q5165492_is_open U ->
      q5165492_is_open V ->
      q5165492_is_open (fun x => U x /\ V x);
  q5165492_open_union :
    forall family : q5165492_event A -> Prop,
      (forall U : q5165492_event A,
        family U -> q5165492_is_open U) ->
      q5165492_is_open
        (fun x =>
          exists U : q5165492_event A,
            family U /\ U x)
}.

Arguments q5165492_is_open {A} _ _.

Inductive q5165492_borel {A : Type}
    (T : q5165492_topological_space A)
    : q5165492_event A -> Prop :=
| q5165492_borel_open :
    forall U : q5165492_event A,
      q5165492_is_open T U ->
      q5165492_borel T U
| q5165492_borel_extensional :
    forall U V : q5165492_event A,
      q5165492_borel T U ->
      q5165492_same_event U V ->
      q5165492_borel T V
| q5165492_borel_complement :
    forall U : q5165492_event A,
      q5165492_borel T U ->
      q5165492_borel T (q5165492_complement U)
| q5165492_borel_countable_union :
    forall U : nat -> q5165492_event A,
      (forall n : nat, q5165492_borel T (U n)) ->
      q5165492_borel T (q5165492_countable_union U).

Definition q5165492_opens_measurable {A : Type}
    (T : q5165492_topological_space A)
    (M : q5165492_sigma_algebra A) : Prop :=
  forall U : q5165492_event A,
    q5165492_is_open T U -> q5165492_measurable M U.

Definition q5165492_is_borel_space {A : Type}
    (T : q5165492_topological_space A)
    (M : q5165492_sigma_algebra A) : Prop :=
  forall U : q5165492_event A,
    q5165492_measurable M U <-> q5165492_borel T U.

Definition q5165492_continuous {A B : Type}
    (TA : q5165492_topological_space A)
    (TB : q5165492_topological_space B)
    (f : A -> B) : Prop :=
  forall U : q5165492_event B,
    q5165492_is_open TB U ->
    q5165492_is_open TA (fun x => U (f x)).

Definition q5165492_real_open
    (U : q5165492_event R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon -> U y.

Inductive q5165492_real_borel : q5165492_event R -> Prop :=
| q5165492_real_borel_open :
    forall U : q5165492_event R,
      q5165492_real_open U ->
      q5165492_real_borel U
| q5165492_real_borel_extensional :
    forall U V : q5165492_event R,
      q5165492_real_borel U ->
      q5165492_same_event U V ->
      q5165492_real_borel V
| q5165492_real_borel_complement :
    forall U : q5165492_event R,
      q5165492_real_borel U ->
      q5165492_real_borel (q5165492_complement U)
| q5165492_real_borel_countable_union :
    forall U : nat -> q5165492_event R,
      (forall n : nat, q5165492_real_borel (U n)) ->
      q5165492_real_borel (q5165492_countable_union U).

Definition q5165492_continuous_to_real {A : Type}
    (T : q5165492_topological_space A)
    (f : A -> R) : Prop :=
  forall U : q5165492_event R,
    q5165492_real_open U ->
    q5165492_is_open T (fun x => U (f x)).

Definition q5165492_measurable_function {A B : Type}
    (MA : q5165492_sigma_algebra A)
    (MB : q5165492_sigma_algebra B)
    (f : A -> B) : Prop :=
  forall U : q5165492_event B,
    q5165492_measurable MB U ->
    q5165492_measurable MA (fun x => U (f x)).

Definition q5165492_measurable_real_function {A : Type}
    (MA : q5165492_sigma_algebra A)
    (f : A -> R) : Prop :=
  forall U : q5165492_event R,
    q5165492_real_borel U ->
    q5165492_measurable MA (fun x => U (f x)).

Fixpoint q5165492_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q5165492_partial_sum u k + u k
  end.

Definition q5165492_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Record q5165492_probability_mass
    (A : Type) (M : q5165492_sigma_algebra A) : Type := {
  q5165492_mass : q5165492_event A -> R;
  q5165492_mass_extensional :
    forall E F : q5165492_event A,
      q5165492_measurable M E ->
      q5165492_measurable M F ->
      q5165492_same_event E F ->
      q5165492_mass E = q5165492_mass F;
  q5165492_mass_empty :
    q5165492_mass q5165492_empty = 0;
  q5165492_mass_full :
    q5165492_mass q5165492_full = 1;
  q5165492_mass_nonnegative :
    forall E : q5165492_event A,
      q5165492_measurable M E ->
      0 <= q5165492_mass E;
  q5165492_mass_countably_additive :
    forall E : nat -> q5165492_event A,
      (forall n : nat, q5165492_measurable M (E n)) ->
      q5165492_pairwise_disjoint E ->
      q5165492_real_sequence_converges
        (fun n =>
          q5165492_partial_sum
            (fun k => q5165492_mass (E k)) n)
        (q5165492_mass (q5165492_countable_union E))
}.

Arguments q5165492_probability_mass A M : clear implicits.
Arguments q5165492_mass {A M} _ _.

Definition q5165492_almost_everywhere {A : Type}
    {M : q5165492_sigma_algebra A}
    (mu : q5165492_probability_mass A M)
    (P : A -> Prop) : Prop :=
  exists N : q5165492_event A,
    q5165492_measurable M N /\
    q5165492_mass mu N = 0 /\
    forall x : A, ~ P x -> N x.

Definition q5165492_ae_equal {A B : Type}
    {M : q5165492_sigma_algebra A}
    (mu : q5165492_probability_mass A M)
    (f g : A -> B) : Prop :=
  q5165492_almost_everywhere mu (fun x => f x = g x).

Definition q5165492_ae_measurable {A B : Type}
    (MA : q5165492_sigma_algebra A)
    (MB : q5165492_sigma_algebra B)
    (mu : q5165492_probability_mass A MA)
    (f : A -> B) : Prop :=
  exists g : A -> B,
    q5165492_measurable_function MA MB g /\
    q5165492_ae_equal mu f g.

Arguments q5165492_ae_measurable {A B} MA MB mu f.

Definition q5165492_ae_measurable_real {A : Type}
    (MA : q5165492_sigma_algebra A)
    (mu : q5165492_probability_mass A MA)
    (f : A -> R) : Prop :=
  exists g : A -> R,
    q5165492_measurable_real_function MA g /\
    q5165492_ae_equal mu f g.

Arguments q5165492_ae_measurable_real {A} MA mu f.

Definition q5165492_bounded {A : Type}
    (f : A -> R) : Prop :=
  exists C : R,
    0 <= C /\ forall x : A, Rabs (f x) <= C.

Definition q5165492_nonnegative {A : Type}
    (f : A -> R) : Prop :=
  forall x : A, 0 <= f x.

Definition q5165492_increasing {A : Type}
    (f : nat -> A -> R) : Prop :=
  forall (n : nat) (x : A), f n x <= f (S n) x.

Definition q5165492_is_indicator {A : Type}
    (E : q5165492_event A)
    (f : A -> R) : Prop :=
  forall x : A,
    (E x /\ f x = 1) \/ (~ E x /\ f x = 0).

Record q5165492_probability_measure
    (A : Type) (M : q5165492_sigma_algebra A) : Type := {
  q5165492_probability_mass_part :
    q5165492_probability_mass A M;
  q5165492_integral : (A -> R) -> R;
  q5165492_integral_ae_extensional :
    forall f g : A -> R,
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part f ->
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part g ->
      q5165492_bounded f ->
      q5165492_bounded g ->
      q5165492_ae_equal
        q5165492_probability_mass_part f g ->
      q5165492_integral f = q5165492_integral g;
  q5165492_integral_indicator :
    forall (E : q5165492_event A) (f : A -> R),
      q5165492_measurable M E ->
      q5165492_is_indicator E f ->
      q5165492_integral f =
      q5165492_mass q5165492_probability_mass_part E;
  q5165492_integral_add :
    forall f g : A -> R,
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part f ->
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part g ->
      q5165492_bounded f ->
      q5165492_bounded g ->
      q5165492_integral (fun x => f x + g x) =
      q5165492_integral f + q5165492_integral g;
  q5165492_integral_scale :
    forall (c : R) (f : A -> R),
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part f ->
      q5165492_bounded f ->
      q5165492_integral (fun x => c * f x) =
      c * q5165492_integral f;
  q5165492_integral_nonnegative :
    forall f : A -> R,
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part f ->
      q5165492_bounded f ->
      q5165492_nonnegative f ->
      0 <= q5165492_integral f;
  q5165492_integral_monotone_convergence :
    forall (f : nat -> A -> R) (g : A -> R),
      (forall n : nat,
        q5165492_ae_measurable_real M
          q5165492_probability_mass_part (f n)) ->
      q5165492_ae_measurable_real M
        q5165492_probability_mass_part g ->
      (forall n : nat, q5165492_bounded (f n)) ->
      q5165492_bounded g ->
      (forall n : nat, q5165492_nonnegative (f n)) ->
      q5165492_increasing f ->
      (forall x : A,
        q5165492_real_sequence_converges
          (fun n => f n x) (g x)) ->
      q5165492_real_sequence_converges
        (fun n => q5165492_integral (f n))
        (q5165492_integral g)
}.

Arguments q5165492_probability_measure A M : clear implicits.
Arguments q5165492_probability_mass_part {A M} _.
Arguments q5165492_integral {A M} _ _.

Record q5165492_filter (I : Type) : Type := {
  q5165492_eventually : (I -> Prop) -> Prop;
  q5165492_eventually_true :
    q5165492_eventually (fun _ => True);
  q5165492_eventually_upward :
    forall P Q : I -> Prop,
      q5165492_eventually P ->
      (forall i : I, P i -> Q i) ->
      q5165492_eventually Q;
  q5165492_eventually_intersection :
    forall P Q : I -> Prop,
      q5165492_eventually P ->
      q5165492_eventually Q ->
      q5165492_eventually (fun i => P i /\ Q i)
}.

Arguments q5165492_eventually {I} _ _.

Definition q5165492_filter_tendsto_real {I : Type}
    (l : q5165492_filter I)
    (u : I -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    q5165492_eventually l
      (fun i => Rabs (u i - limit) < epsilon).

Definition q5165492_tendsto_in_distribution
    {I E : Type}
    {Omega : I -> Type}
    {OmegaLimit : Type}
    (TE : q5165492_topological_space E)
    (ME : q5165492_sigma_algebra E)
    (MOmega : forall i : I,
      q5165492_sigma_algebra (Omega i))
    (MOLimit : q5165492_sigma_algebra OmegaLimit)
    (mu : forall i : I,
      q5165492_probability_measure (Omega i) (MOmega i))
    (muLimit : q5165492_probability_measure OmegaLimit MOLimit)
    (X : forall i : I, Omega i -> E)
    (l : q5165492_filter I)
    (Z : OmegaLimit -> E) : Prop :=
  (forall i : I,
    q5165492_ae_measurable
      (MOmega i) ME
      (q5165492_probability_mass_part (mu i))
      (X i)) /\
  q5165492_ae_measurable
    MOLimit ME
    (q5165492_probability_mass_part muLimit)
    Z /\
  forall h : E -> R,
    q5165492_continuous_to_real TE h ->
    q5165492_bounded h ->
    q5165492_filter_tendsto_real l
      (fun i =>
        q5165492_integral (mu i)
          (fun omega => h (X i omega)))
      (q5165492_integral muLimit
        (fun omega => h (Z omega))).

Arguments q5165492_tendsto_in_distribution
  {I E Omega OmegaLimit}
  TE ME MOmega MOLimit mu muLimit X l Z.

Theorem q5165492_continuous_mapping_theorem :
  forall (I E F : Type)
         (Omega : I -> Type)
         (OmegaLimit : Type)
         (TE : q5165492_topological_space E)
         (TF : q5165492_topological_space F)
         (ME : q5165492_sigma_algebra E)
         (MF : q5165492_sigma_algebra F)
         (MOmega : forall i : I,
           q5165492_sigma_algebra (Omega i))
         (MOLimit : q5165492_sigma_algebra OmegaLimit)
         (mu : forall i : I,
           q5165492_probability_measure (Omega i) (MOmega i))
         (muLimit :
           q5165492_probability_measure OmegaLimit MOLimit)
         (X : forall i : I, Omega i -> E)
         (l : q5165492_filter I)
         (Z : OmegaLimit -> E)
         (g : E -> F),
    q5165492_opens_measurable TE ME ->
    q5165492_is_borel_space TF MF ->
    q5165492_continuous TE TF g ->
    q5165492_tendsto_in_distribution
      TE ME MOmega MOLimit mu muLimit X l Z ->
    q5165492_tendsto_in_distribution
      TF MF MOmega MOLimit mu muLimit
      (fun (i : I) (omega : Omega i) => g (X i omega))
      l
      (fun omega : OmegaLimit => g (Z omega)).
Admitted.
