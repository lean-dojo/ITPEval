(* Statement-only formalization of Thousand Theorems corpus artifact Q25378690
   (thousand-theorems__rocq__Q25378690), "Ionescu-Tulcea theorem":
   measurable Markov kernels on successive trajectory prefixes extend to a
   Markov kernel on infinite trajectories with the prescribed
   finite-dimensional distributions. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition Event (A : Type) := A -> Prop.
Definition SigmaAlgebra (A : Type) := Event A -> Prop.

Definition empty_event {A : Type} : Event A := fun _ => False.
Definition full_event {A : Type} : Event A := fun _ => True.
Definition event_complement {A : Type} (E : Event A) : Event A :=
  fun x => ~ E x.
Definition countable_union {A : Type} (E : nat -> Event A) : Event A :=
  fun x => exists n, E n x.

Definition pairwise_disjoint {A : Type} (E : nat -> Event A) : Prop :=
  forall i j x, i <> j -> ~ (E i x /\ E j x).

Record IsSigmaAlgebra {A : Type} (M : SigmaAlgebra A) : Prop := {
  sigma_empty : M empty_event;
  sigma_ext :
    forall E F, M E -> (forall x, E x <-> F x) -> M F;
  sigma_complement :
    forall E, M E -> M (event_complement E);
  sigma_countable_union :
    forall E, (forall n, M (E n)) -> M (countable_union E)
}.

Inductive Borel : Event R -> Prop :=
| borel_open_ray :
    forall c : R, Borel (fun x => x < c)
| borel_empty :
    Borel empty_event
| borel_ext :
    forall E F, Borel E -> (forall x, E x <-> F x) -> Borel F
| borel_complement :
    forall E, Borel E -> Borel (event_complement E)
| borel_countable_union :
    forall E, (forall n, Borel (E n)) -> Borel (countable_union E).

Definition MeasurableFunction {A B : Type}
    (MA : SigmaAlgebra A) (MB : SigmaAlgebra B) (f : A -> B) : Prop :=
  forall E, MB E -> MA (fun x => E (f x)).

Definition Bounded {A : Type} (f : A -> R) : Prop :=
  exists C : R, 0 <= C /\ forall x, Rabs (f x) <= C.

Definition Nonnegative {A : Type} (f : A -> R) : Prop :=
  forall x, 0 <= f x.

Definition IncreasingSequence {A : Type} (f : nat -> A -> R) : Prop :=
  forall n x, f n x <= f (S n) x.

Definition ConvergesTo (u : nat -> R) (l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat -> Rabs (u n - l) < eps.

Fixpoint partial_sum (u : nat -> R) (n : nat) : R :=
  match n with
  | O => u O
  | S m => partial_sum u m + u (S m)
  end.

Definition IsIndicator {A : Type} (E : Event A) (f : A -> R) : Prop :=
  forall x, (E x /\ f x = 1) \/ (~ E x /\ f x = 0).

Record ProbabilityMeasure (A : Type) (M : SigmaAlgebra A) : Type := {
  probability_mass : Event A -> R;
  probability_integral : (A -> R) -> R;

  probability_mass_ext :
    forall E F, M E -> M F ->
      (forall x, E x <-> F x) ->
      probability_mass E = probability_mass F;
  probability_mass_empty :
    probability_mass empty_event = 0;
  probability_mass_full :
    probability_mass full_event = 1;
  probability_mass_nonnegative :
    forall E, M E -> 0 <= probability_mass E;
  probability_mass_countably_additive :
    forall E, (forall n, M (E n)) ->
      pairwise_disjoint E ->
      ConvergesTo
        (fun n => partial_sum (fun k => probability_mass (E k)) n)
        (probability_mass (countable_union E));

  probability_integral_ext :
    forall f g, MeasurableFunction M Borel f ->
      MeasurableFunction M Borel g ->
      Bounded f -> Bounded g ->
      (forall x, f x = g x) ->
      probability_integral f = probability_integral g;
  probability_integral_indicator :
    forall E f, M E -> IsIndicator E f ->
      probability_integral f = probability_mass E;
  probability_integral_add :
    forall f g, MeasurableFunction M Borel f ->
      MeasurableFunction M Borel g ->
      Bounded f -> Bounded g ->
      probability_integral (fun x => f x + g x) =
        probability_integral f + probability_integral g;
  probability_integral_scale :
    forall (c : R) f, MeasurableFunction M Borel f ->
      Bounded f ->
      probability_integral (fun x => c * f x) =
        c * probability_integral f;
  probability_integral_nonnegative :
    forall f, MeasurableFunction M Borel f ->
      Bounded f -> Nonnegative f ->
      0 <= probability_integral f;
  probability_integral_monotone_convergence :
    forall (f : nat -> A -> R) g,
      (forall n, MeasurableFunction M Borel (f n)) ->
      MeasurableFunction M Borel g ->
      (forall n, Bounded (f n)) ->
      Bounded g ->
      (forall n, Nonnegative (f n)) ->
      IncreasingSequence f ->
      (forall x, ConvergesTo (fun n => f n x) (g x)) ->
      ConvergesTo (fun n => probability_integral (f n))
        (probability_integral g)
}.

Arguments probability_mass {A M} _ _.
Arguments probability_integral {A M} _ _.

Record MarkovKernel (A B : Type)
    (MA : SigmaAlgebra A) (MB : SigmaAlgebra B) : Type := {
  kernel_at : A -> ProbabilityMeasure B MB;
  kernel_mass_measurable :
    forall E, MB E ->
      MeasurableFunction MA Borel
        (fun x => probability_mass (kernel_at x) E);
  kernel_integral_measurable :
    forall f, MeasurableFunction MB Borel f ->
      Bounded f ->
      MeasurableFunction MA Borel
        (fun x => probability_integral (kernel_at x) f)
}.

Arguments kernel_at {A B MA MB} _ _.

Inductive ProductSigma {A B : Type}
    (MA : SigmaAlgebra A) (MB : SigmaAlgebra B) : SigmaAlgebra (A * B) :=
| product_left :
    forall E, MA E -> ProductSigma MA MB (fun z => E (fst z))
| product_right :
    forall E, MB E -> ProductSigma MA MB (fun z => E (snd z))
| product_empty :
    ProductSigma MA MB empty_event
| product_ext :
    forall E F, ProductSigma MA MB E ->
      (forall z, E z <-> F z) ->
      ProductSigma MA MB F
| product_complement :
    forall E, ProductSigma MA MB E ->
      ProductSigma MA MB (event_complement E)
| product_countable_union :
    forall E, (forall n, ProductSigma MA MB (E n)) ->
      ProductSigma MA MB (countable_union E).

Fixpoint Prefix (X : nat -> Type) (n : nat) : Type :=
  match n with
  | O => X O
  | S m => (Prefix X m * X (S m))%type
  end.

Fixpoint PrefixSigma (X : nat -> Type)
    (MX : forall n, SigmaAlgebra (X n)) (n : nat)
    : SigmaAlgebra (Prefix X n) :=
  match n as k return SigmaAlgebra (Prefix X k) with
  | O => MX O
  | S m => ProductSigma (PrefixSigma X MX m) (MX (S m))
  end.

Definition Path (X : nat -> Type) := forall n : nat, X n.

Fixpoint restrict_path (X : nat -> Type) (n : nat)
    (omega : Path X) : Prefix X n :=
  match n as k return Prefix X k with
  | O => omega O
  | S m => (restrict_path X m omega, omega (S m))
  end.

Inductive PathSigma (X : nat -> Type)
    (MX : forall n, SigmaAlgebra (X n)) : SigmaAlgebra (Path X) :=
| path_cylinder :
    forall n E, PrefixSigma X MX n E ->
      PathSigma X MX (fun omega => E (restrict_path X n omega))
| path_empty :
    PathSigma X MX empty_event
| path_ext :
    forall E F, PathSigma X MX E ->
      (forall omega, E omega <-> F omega) ->
      PathSigma X MX F
| path_complement :
    forall E, PathSigma X MX E ->
      PathSigma X MX (event_complement E)
| path_countable_union :
    forall E, (forall n, PathSigma X MX (E n)) ->
      PathSigma X MX (countable_union E).

Inductive FiniteTrajectoryExpectation
    (X : nat -> Type)
    (MX : forall n, SigmaAlgebra (X n))
    (kappa : forall n,
      MarkovKernel (Prefix X n) (X (S n))
        (PrefixSigma X MX n) (MX (S n)))
    : forall a b, Prefix X a -> (Prefix X b -> R) -> R -> Prop :=
| finite_expectation_refl :
    forall a (x : Prefix X a) (f : Prefix X a -> R),
      FiniteTrajectoryExpectation X MX kappa a a x f (f x)
| finite_expectation_step :
    forall a b (x : Prefix X a) (f : Prefix X b -> R)
      (g : X (S a) -> R),
      MeasurableFunction (MX (S a)) Borel g ->
      Bounded g ->
      (forall y,
        FiniteTrajectoryExpectation X MX kappa
          (S a) b (x, y) f (g y)) ->
      FiniteTrajectoryExpectation X MX kappa a b x f
        (probability_integral (kernel_at (kappa a) x) g).

Theorem ionescu_tulcea_traj :
  forall (X : nat -> Type)
    (MX : forall n, SigmaAlgebra (X n)),
    (forall n, IsSigmaAlgebra (MX n)) ->
    forall (kappa : forall n,
      MarkovKernel (Prefix X n) (X (S n))
        (PrefixSigma X MX n) (MX (S n))),
    exists traj : forall a,
      MarkovKernel (Prefix X a) (Path X)
        (PrefixSigma X MX a) (PathSigma X MX),
      forall (a : nat) (x : Prefix X a) (b : nat)
        (f : Prefix X b -> R),
        (a <= b)%nat ->
        MeasurableFunction (PrefixSigma X MX b) Borel f ->
        Bounded f ->
        exists r : R,
          FiniteTrajectoryExpectation X MX kappa a b x f r /\
          probability_integral (kernel_at (traj a) x)
            (fun omega => f (restrict_path X b omega)) = r.
Admitted.
