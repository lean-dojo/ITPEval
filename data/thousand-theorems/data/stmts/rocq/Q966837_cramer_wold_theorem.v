(*
  Statement-only formalization of Thousand Theorems corpus artifact Q966837
  (thousand-theorems__rocq__Q966837), "Cramér–Wold theorem": convergence in
  distribution of random variables in a finite-dimensional real inner-product
  space is equivalent to convergence in distribution of every scalar
  projection. This file contains no proof.
*)

From Stdlib Require Import Reals PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q966837_event (A : Type) : Type := A -> Prop.

Definition q966837_empty {A : Type} : q966837_event A :=
  fun _ => False.

Definition q966837_full {A : Type} : q966837_event A :=
  fun _ => True.

Definition q966837_complement {A : Type}
    (U : q966837_event A) : q966837_event A :=
  fun x => ~ U x.

Definition q966837_countable_union {A : Type}
    (U : nat -> q966837_event A) : q966837_event A :=
  fun x => exists n : nat, U n x.

Definition q966837_preimage {A B : Type}
    (f : A -> B) (U : q966837_event B) : q966837_event A :=
  fun x => U (f x).

Definition q966837_same_event {A : Type}
    (U W : q966837_event A) : Prop :=
  forall x : A, U x <-> W x.

Definition q966837_subset {A : Type}
    (U W : q966837_event A) : Prop :=
  forall x : A, U x -> W x.

Definition q966837_disjoint {A : Type}
    (U W : q966837_event A) : Prop :=
  forall x : A, ~ (U x /\ W x).

Definition q966837_pairwise_disjoint {A : Type}
    (U : nat -> q966837_event A) : Prop :=
  forall i j : nat,
    i <> j -> q966837_disjoint (U i) (U j).

Record q966837_measurable_space (A : Type) : Type := {
  q966837_measurable : q966837_event A -> Prop;
  q966837_measurable_extensional :
    forall U W : q966837_event A,
      q966837_same_event U W ->
      (q966837_measurable U <-> q966837_measurable W);
  q966837_measurable_empty :
    q966837_measurable q966837_empty;
  q966837_measurable_complement :
    forall U : q966837_event A,
      q966837_measurable U ->
      q966837_measurable (q966837_complement U);
  q966837_measurable_countable_union :
    forall U : nat -> q966837_event A,
      (forall n : nat, q966837_measurable (U n)) ->
      q966837_measurable (q966837_countable_union U)
}.

Arguments q966837_measurable {A} _ _.

Definition q966837_measurable_function {A B : Type}
    (MA : q966837_measurable_space A)
    (MB : q966837_measurable_space B)
    (f : A -> B) : Prop :=
  forall U : q966837_event B,
    q966837_measurable MB U ->
    q966837_measurable MA (q966837_preimage f U).

Fixpoint q966837_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q966837_partial_sum u k + u k
  end.

Definition q966837_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q966837_infimum
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> bound <= value) /\
  (forall lower : R,
    (forall value : R, values value -> lower <= value) ->
    lower <= bound).

Record q966837_probability_measure
    (A : Type) (M : q966837_measurable_space A) : Type := {
  q966837_mass : q966837_event A -> R;
  q966837_mass_extensional :
    forall U W : q966837_event A,
      q966837_same_event U W ->
      q966837_mass U = q966837_mass W;
  q966837_mass_nonnegative :
    forall U : q966837_event A, 0 <= q966837_mass U;
  q966837_mass_empty :
    q966837_mass q966837_empty = 0;
  q966837_mass_full :
    q966837_mass q966837_full = 1;
  q966837_mass_monotone :
    forall U W : q966837_event A,
      q966837_subset U W ->
      q966837_mass U <= q966837_mass W;
  q966837_mass_trimmed :
    forall U : q966837_event A,
      q966837_infimum
        (fun value : R =>
          exists W : q966837_event A,
            q966837_measurable M W /\
            q966837_subset U W /\
            value = q966837_mass W)
        (q966837_mass U);
  q966837_mass_countably_additive :
    forall U : nat -> q966837_event A,
      (forall n : nat, q966837_measurable M (U n)) ->
      q966837_pairwise_disjoint U ->
      q966837_sequence_converges
        (fun n =>
          q966837_partial_sum
            (fun k => q966837_mass (U k)) n)
        (q966837_mass (q966837_countable_union U))
}.

Arguments q966837_probability_measure A M : clear implicits.
Arguments q966837_mass {A M} _ _.

Definition q966837_ae_equal {A B : Type}
    {M : q966837_measurable_space A}
    (P : q966837_probability_measure A M)
    (f g : A -> B) : Prop :=
  exists N : q966837_event A,
    q966837_mass P N = 0 /\
    forall x : A, ~ N x -> f x = g x.

Definition q966837_ae_measurable {A B : Type}
    (MA : q966837_measurable_space A)
    (MB : q966837_measurable_space B)
    (P : q966837_probability_measure A MA)
    (f : A -> B) : Prop :=
  exists g : A -> B,
    q966837_measurable_function MA MB g /\
    q966837_ae_equal P f g.

Record q966837_real_inner_product_space (E : Type) : Type := {
  q966837_zero : E;
  q966837_add : E -> E -> E;
  q966837_neg : E -> E;
  q966837_smul : R -> E -> E;
  q966837_inner : E -> E -> R;
  q966837_add_assoc :
    forall x y z : E,
      q966837_add x (q966837_add y z) =
      q966837_add (q966837_add x y) z;
  q966837_add_comm :
    forall x y : E, q966837_add x y = q966837_add y x;
  q966837_zero_add :
    forall x : E, q966837_add q966837_zero x = x;
  q966837_neg_add :
    forall x : E,
      q966837_add (q966837_neg x) x = q966837_zero;
  q966837_one_smul :
    forall x : E, q966837_smul 1 x = x;
  q966837_mul_smul :
    forall (a b : R) (x : E),
      q966837_smul (a * b) x =
      q966837_smul a (q966837_smul b x);
  q966837_add_smul :
    forall (a b : R) (x : E),
      q966837_smul (a + b) x =
      q966837_add (q966837_smul a x) (q966837_smul b x);
  q966837_smul_add :
    forall (a : R) (x y : E),
      q966837_smul a (q966837_add x y) =
      q966837_add (q966837_smul a x) (q966837_smul a y);
  q966837_zero_smul :
    forall x : E, q966837_smul 0 x = q966837_zero;
  q966837_smul_zero :
    forall a : R, q966837_smul a q966837_zero = q966837_zero;
  q966837_neg_eq_smul :
    forall x : E, q966837_neg x = q966837_smul (-1) x;
  q966837_inner_add_left :
    forall x y z : E,
      q966837_inner (q966837_add x y) z =
      q966837_inner x z + q966837_inner y z;
  q966837_inner_smul_left :
    forall (a : R) (x y : E),
      q966837_inner (q966837_smul a x) y =
      a * q966837_inner x y;
  q966837_inner_symm :
    forall x y : E, q966837_inner x y = q966837_inner y x;
  q966837_inner_nonnegative :
    forall x : E, 0 <= q966837_inner x x;
  q966837_inner_eq_zero :
    forall x : E,
      q966837_inner x x = 0 <-> x = q966837_zero;
  q966837_finite_orthonormal_basis :
    exists (dimension : nat) (basis : nat -> E),
      (forall i j : nat,
        (i < dimension)%nat ->
        (j < dimension)%nat ->
        q966837_inner (basis i) (basis j) =
          if Nat.eq_dec i j then 1 else 0) /\
      forall x : E,
        x =
        (fix sum (n : nat) : E :=
          match n with
          | O => q966837_zero
          | S k =>
              q966837_add
                (sum k)
                (q966837_smul
                  (q966837_inner x (basis k))
                  (basis k))
          end) dimension
}.

Arguments q966837_zero {E} _.
Arguments q966837_add {E} _ _ _.
Arguments q966837_neg {E} _ _.
Arguments q966837_smul {E} _ _ _.
Arguments q966837_inner {E} _ _ _.

Definition q966837_sub {E : Type}
    (V : q966837_real_inner_product_space E)
    (x y : E) : E :=
  q966837_add V x (q966837_neg V y).

Definition q966837_norm {E : Type}
    (V : q966837_real_inner_product_space E)
    (x : E) : R :=
  sqrt (q966837_inner V x x).

Definition q966837_metric_open {E : Type}
    (V : q966837_real_inner_product_space E)
    (U : q966837_event E) : Prop :=
  forall x : E,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : E,
        q966837_norm V (q966837_sub V y x) < epsilon ->
        U y.

Definition q966837_metric_closed {E : Type}
    (V : q966837_real_inner_product_space E)
    (F : q966837_event E) : Prop :=
  q966837_metric_open V (q966837_complement F).

Inductive q966837_borel {E : Type}
    (V : q966837_real_inner_product_space E)
    : q966837_event E -> Prop :=
| q966837_borel_open :
    forall U : q966837_event E,
      q966837_metric_open V U ->
      q966837_borel V U
| q966837_borel_empty :
    q966837_borel V q966837_empty
| q966837_borel_extensional :
    forall U W : q966837_event E,
      q966837_borel V U ->
      q966837_same_event U W ->
      q966837_borel V W
| q966837_borel_complement :
    forall U : q966837_event E,
      q966837_borel V U ->
      q966837_borel V (q966837_complement U)
| q966837_borel_countable_union :
    forall U : nat -> q966837_event E,
      (forall n : nat, q966837_borel V (U n)) ->
      q966837_borel V (q966837_countable_union U).

Definition q966837_borel_space {E : Type}
    (V : q966837_real_inner_product_space E)
    : q966837_measurable_space E :=
  {|
    q966837_measurable := q966837_borel V;
    q966837_measurable_extensional :=
      fun U W h =>
        conj
          (fun hU =>
            @q966837_borel_extensional E V U W hU h)
          (fun hW =>
            @q966837_borel_extensional E V W U hW
              (fun x => iff_sym (h x)));
    q966837_measurable_empty := @q966837_borel_empty E V;
    q966837_measurable_complement :=
      @q966837_borel_complement E V;
    q966837_measurable_countable_union :=
      @q966837_borel_countable_union E V
  |}.

Definition q966837_real_open
    (U : q966837_event R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q966837_real_closed
    (F : q966837_event R) : Prop :=
  q966837_real_open (q966837_complement F).

Inductive q966837_real_borel : q966837_event R -> Prop :=
| q966837_real_borel_open :
    forall U : q966837_event R,
      q966837_real_open U ->
      q966837_real_borel U
| q966837_real_borel_empty :
    q966837_real_borel q966837_empty
| q966837_real_borel_extensional :
    forall U W : q966837_event R,
      q966837_real_borel U ->
      q966837_same_event U W ->
      q966837_real_borel W
| q966837_real_borel_complement :
    forall U : q966837_event R,
      q966837_real_borel U ->
      q966837_real_borel (q966837_complement U)
| q966837_real_borel_countable_union :
    forall U : nat -> q966837_event R,
      (forall n : nat, q966837_real_borel (U n)) ->
      q966837_real_borel (q966837_countable_union U).

Definition q966837_real_borel_space : q966837_measurable_space R :=
  {|
    q966837_measurable := q966837_real_borel;
    q966837_measurable_extensional :=
      fun U W h =>
        conj
          (fun hU =>
            @q966837_real_borel_extensional U W hU h)
          (fun hW =>
            @q966837_real_borel_extensional W U hW
              (fun x => iff_sym (h x)));
    q966837_measurable_empty := q966837_real_borel_empty;
    q966837_measurable_complement :=
      @q966837_real_borel_complement;
    q966837_measurable_countable_union :=
      @q966837_real_borel_countable_union
  |}.

Definition q966837_limsup_le
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        u n <= limit + epsilon.

Definition q966837_vector_tendsto_in_distribution
    {E Omega Omega' : Type}
    (V : q966837_real_inner_product_space E)
    (MOmega : q966837_measurable_space Omega)
    (MOmega' : q966837_measurable_space Omega')
    (P : q966837_probability_measure Omega MOmega)
    (P' : q966837_probability_measure Omega' MOmega')
  (X : nat -> Omega -> E)
    (X' : Omega' -> E) : Prop :=
  (forall n : nat,
    @q966837_ae_measurable
      Omega E MOmega (q966837_borel_space V) P (X n)) /\
  @q966837_ae_measurable
    Omega' E MOmega' (q966837_borel_space V) P' X' /\
  forall F : q966837_event E,
    q966837_metric_closed V F ->
    q966837_limsup_le
      (fun n => q966837_mass P (q966837_preimage (X n) F))
      (q966837_mass P' (q966837_preimage X' F)).

Definition q966837_scalar_tendsto_in_distribution
    {Omega Omega' : Type}
    (MOmega : q966837_measurable_space Omega)
    (MOmega' : q966837_measurable_space Omega')
    (P : q966837_probability_measure Omega MOmega)
    (P' : q966837_probability_measure Omega' MOmega')
    (Y : nat -> Omega -> R)
    (Y' : Omega' -> R) : Prop :=
  (forall n : nat,
    @q966837_ae_measurable
      Omega R MOmega q966837_real_borel_space P (Y n)) /\
  @q966837_ae_measurable
    Omega' R MOmega' q966837_real_borel_space P' Y' /\
  forall F : q966837_event R,
    q966837_real_closed F ->
    q966837_limsup_le
      (fun n => q966837_mass P (q966837_preimage (Y n) F))
      (q966837_mass P' (q966837_preimage Y' F)).

Theorem q966837_cramer_wold_theorem :
  forall (E Omega Omega' : Type)
         (V : q966837_real_inner_product_space E)
         (MOmega : q966837_measurable_space Omega)
         (MOmega' : q966837_measurable_space Omega')
         (P : q966837_probability_measure Omega MOmega)
         (P' : q966837_probability_measure Omega' MOmega')
         (X : nat -> Omega -> E)
         (X' : Omega' -> E),
    @q966837_ae_measurable
      Omega' E MOmega' (q966837_borel_space V) P' X' ->
    (forall n : nat,
      @q966837_ae_measurable
        Omega E MOmega (q966837_borel_space V) P (X n)) ->
    @q966837_vector_tendsto_in_distribution
      E Omega Omega' V MOmega MOmega' P P' X X' <->
    forall t : E,
      @q966837_scalar_tendsto_in_distribution
        Omega Omega' MOmega MOmega' P P'
        (fun n omega => q966837_inner V (X n omega) t)
        (fun omega => q966837_inner V (X' omega) t).
Admitted.
