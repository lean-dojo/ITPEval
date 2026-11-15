(*
  Statement-only formalization of Thousand Theorems corpus artifact Q338886
  (thousand-theorems__rocq__Q338886), "Divergence theorem": the Bochner
  integral of the divergence of a normed-space-valued vector field on a
  finite-dimensional real box equals the signed sum of its face integrals,
  allowing a countable exceptional set for differentiability. This file
  contains no proof.
*)

From Stdlib Require Import
  Reals
  Arith
  Lists.List
  ClassicalDescription
  ClassicalEpsilon.

Import ListNotations.
Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q338886_set (A : Type) : Type := A -> Prop.

Definition q338886_valid_point (dimension : nat) (x : list R) : Prop :=
  length x = dimension.

Definition q338886_empty (dimension : nat) : q338886_set (list R) :=
  fun _ => False.

Definition q338886_full (dimension : nat) : q338886_set (list R) :=
  q338886_valid_point dimension.

Definition q338886_complement
    (dimension : nat) (S : q338886_set (list R)) :
    q338886_set (list R) :=
  fun x => q338886_valid_point dimension x /\ ~ S x.

Definition q338886_countable_union
    (S : nat -> q338886_set (list R)) : q338886_set (list R) :=
  fun x => exists n : nat, S n x.

Definition q338886_same_set
    (S T : q338886_set (list R)) : Prop :=
  forall x : list R, S x <-> T x.

Definition q338886_disjoint
    (S T : q338886_set (list R)) : Prop :=
  forall x : list R, ~ (S x /\ T x).

Definition q338886_pairwise_disjoint
    (S : nat -> q338886_set (list R)) : Prop :=
  forall i j : nat,
    i <> j -> q338886_disjoint (S i) (S j).

Definition q338886_nth_real (x : list R) (i : nat) : R :=
  nth i x 0.

Fixpoint q338886_real_product
    (count : nat) (u : nat -> R) : R :=
  match count with
  | O => 1
  | S k => q338886_real_product k u * u k
  end.

Definition q338886_box
    (dimension : nat) (a b : list R) : q338886_set (list R) :=
  fun x =>
    q338886_valid_point dimension a /\
    q338886_valid_point dimension b /\
    q338886_valid_point dimension x /\
    forall i : nat,
      (i < dimension)%nat ->
      q338886_nth_real a i <= q338886_nth_real x i /\
      q338886_nth_real x i <= q338886_nth_real b i.

Definition q338886_open_box
    (dimension : nat) (a b : list R) : q338886_set (list R) :=
  fun x =>
    q338886_valid_point dimension a /\
    q338886_valid_point dimension b /\
    q338886_valid_point dimension x /\
    forall i : nat,
      (i < dimension)%nat ->
      q338886_nth_real a i < q338886_nth_real x i /\
      q338886_nth_real x i < q338886_nth_real b i.

Definition q338886_half_open_box
    (dimension : nat) (a b : list R) : q338886_set (list R) :=
  fun x =>
    q338886_valid_point dimension a /\
    q338886_valid_point dimension b /\
    q338886_valid_point dimension x /\
    forall i : nat,
      (i < dimension)%nat ->
      q338886_nth_real a i < q338886_nth_real x i /\
      q338886_nth_real x i <= q338886_nth_real b i.

Definition q338886_sigma_class
    (dimension : nat)
    (C : q338886_set (q338886_set (list R))) : Prop :=
  C (q338886_empty dimension) /\
  (forall S T : q338886_set (list R),
    q338886_same_set S T -> C S -> C T) /\
  (forall S : q338886_set (list R),
    C S -> C (q338886_complement dimension S)) /\
  (forall S : nat -> q338886_set (list R),
    (forall n : nat, C (S n)) ->
    C (q338886_countable_union S)).

Inductive q338886_ennreal : Type :=
| q338886_ennreal_finite : R -> q338886_ennreal
| q338886_ennreal_infinity : q338886_ennreal.

Definition q338886_ennreal_valid (x : q338886_ennreal) : Prop :=
  match x with
  | q338886_ennreal_finite value => 0 <= value
  | q338886_ennreal_infinity => True
  end.

Definition q338886_ennreal_zero : q338886_ennreal :=
  q338886_ennreal_finite 0.

Definition q338886_ennreal_eq
    (x y : q338886_ennreal) : Prop :=
  match x, y with
  | q338886_ennreal_finite a, q338886_ennreal_finite b => a = b
  | q338886_ennreal_infinity, q338886_ennreal_infinity => True
  | _, _ => False
  end.

Definition q338886_ennreal_le
    (x y : q338886_ennreal) : Prop :=
  match x, y with
  | q338886_ennreal_finite a, q338886_ennreal_finite b => a <= b
  | q338886_ennreal_finite _, q338886_ennreal_infinity => True
  | q338886_ennreal_infinity, q338886_ennreal_finite _ => False
  | q338886_ennreal_infinity, q338886_ennreal_infinity => True
  end.

Definition q338886_ennreal_add
    (x y : q338886_ennreal) : q338886_ennreal :=
  match x, y with
  | q338886_ennreal_finite a, q338886_ennreal_finite b =>
      q338886_ennreal_finite (a + b)
  | _, _ => q338886_ennreal_infinity
  end.

Definition q338886_ennreal_mul
    (x y : q338886_ennreal) : q338886_ennreal :=
  match x, y with
  | q338886_ennreal_finite a, q338886_ennreal_finite b =>
      q338886_ennreal_finite (a * b)
  | q338886_ennreal_finite a, q338886_ennreal_infinity
  | q338886_ennreal_infinity, q338886_ennreal_finite a =>
      if Req_EM_T a 0
      then q338886_ennreal_zero
      else q338886_ennreal_infinity
  | q338886_ennreal_infinity, q338886_ennreal_infinity =>
      q338886_ennreal_infinity
  end.

Fixpoint q338886_ennreal_partial_sum
    (u : nat -> q338886_ennreal)
    (n : nat) : q338886_ennreal :=
  match n with
  | O => q338886_ennreal_zero
  | S k =>
      q338886_ennreal_add
        (q338886_ennreal_partial_sum u k) (u k)
  end.

Definition q338886_ennreal_supremum
    (values : q338886_ennreal -> Prop)
    (bound : q338886_ennreal) : Prop :=
  q338886_ennreal_valid bound /\
  (forall value : q338886_ennreal,
    values value -> q338886_ennreal_le value bound) /\
  forall upper : q338886_ennreal,
    q338886_ennreal_valid upper ->
    (forall value : q338886_ennreal,
      values value -> q338886_ennreal_le value upper) ->
    q338886_ennreal_le bound upper.

Definition q338886_ennreal_series_sum
    (u : nat -> q338886_ennreal)
    (sum : q338886_ennreal) : Prop :=
  q338886_ennreal_supremum
    (fun value =>
      exists n : nat,
        q338886_ennreal_eq value
          (q338886_ennreal_partial_sum u n))
    sum.

Definition q338886_ennreal_represents
    (x : q338886_ennreal) (value : R) : Prop :=
  0 <= value /\
  q338886_ennreal_eq x (q338886_ennreal_finite value).

Definition q338886_ennreal_finite_value
    (x : q338886_ennreal) : Prop :=
  exists value : R, q338886_ennreal_represents x value.

Record q338886_lebesgue_measure_space (dimension : nat) : Type := {
  q338886_measurable : q338886_set (list R) -> Prop;
  q338886_measurable_dimension :
    forall S : q338886_set (list R),
      q338886_measurable S ->
      forall x : list R, S x -> q338886_valid_point dimension x;
  q338886_measurable_extensional :
    forall S T : q338886_set (list R),
      q338886_same_set S T ->
      (q338886_measurable S <-> q338886_measurable T);
  q338886_measurable_empty :
    q338886_measurable (q338886_empty dimension);
  q338886_measurable_complement :
    forall S : q338886_set (list R),
      q338886_measurable S ->
      q338886_measurable (q338886_complement dimension S);
  q338886_measurable_countable_union :
    forall S : nat -> q338886_set (list R),
      (forall n : nat, q338886_measurable (S n)) ->
      q338886_measurable (q338886_countable_union S);
  q338886_measurable_open_box :
    forall a b : list R,
      q338886_valid_point dimension a ->
      q338886_valid_point dimension b ->
      q338886_measurable (q338886_open_box dimension a b);
  q338886_measurable_borel_minimal :
    forall C : q338886_set (q338886_set (list R)),
      q338886_sigma_class dimension C ->
      (forall a b : list R,
        q338886_valid_point dimension a ->
        q338886_valid_point dimension b ->
        C (q338886_open_box dimension a b)) ->
      forall S : q338886_set (list R),
        q338886_measurable S -> C S;
  q338886_measure : q338886_set (list R) -> q338886_ennreal;
  q338886_measure_valid :
    forall S : q338886_set (list R),
      q338886_ennreal_valid (q338886_measure S);
  q338886_measure_extensional :
    forall S T : q338886_set (list R),
      q338886_same_set S T ->
      q338886_ennreal_eq
        (q338886_measure S) (q338886_measure T);
  q338886_measure_empty :
    q338886_ennreal_eq
      (q338886_measure (q338886_empty dimension))
      q338886_ennreal_zero;
  q338886_measure_monotone :
    forall S T : q338886_set (list R),
      (forall x : list R, S x -> T x) ->
      q338886_ennreal_le
        (q338886_measure S) (q338886_measure T);
  q338886_measure_trim :
    forall S : q338886_set (list R),
      (forall x : list R, S x -> q338886_valid_point dimension x) ->
      exists T : q338886_set (list R),
        q338886_measurable T /\
        (forall x : list R, S x -> T x) /\
        q338886_ennreal_eq
          (q338886_measure T) (q338886_measure S);
  q338886_measure_countable_additive :
    forall S : nat -> q338886_set (list R),
      (forall n : nat, q338886_measurable (S n)) ->
      q338886_pairwise_disjoint S ->
      q338886_ennreal_series_sum
        (fun n => q338886_measure (S n))
        (q338886_measure (q338886_countable_union S));
  q338886_measure_half_open_box :
    forall a b : list R,
      q338886_valid_point dimension a ->
      q338886_valid_point dimension b ->
      q338886_ennreal_eq
        (q338886_measure (q338886_half_open_box dimension a b))
        (q338886_ennreal_finite
          (q338886_real_product dimension
            (fun i =>
              Rmax
                (q338886_nth_real b i -
                 q338886_nth_real a i) 0)))
}.

Arguments q338886_measurable {dimension} _ _.
Arguments q338886_measure {dimension} _ _.

Record q338886_normed_real_vector_space (E : Type) : Type := {
  q338886_zero : E;
  q338886_add : E -> E -> E;
  q338886_neg : E -> E;
  q338886_smul : R -> E -> E;
  q338886_norm : E -> R;
  q338886_add_assoc :
    forall x y z : E,
      q338886_add x (q338886_add y z) =
      q338886_add (q338886_add x y) z;
  q338886_add_comm :
    forall x y : E, q338886_add x y = q338886_add y x;
  q338886_add_zero :
    forall x : E, q338886_add x q338886_zero = x;
  q338886_add_neg :
    forall x : E,
      q338886_add x (q338886_neg x) = q338886_zero;
  q338886_one_smul :
    forall x : E, q338886_smul 1 x = x;
  q338886_mul_smul :
    forall (a b : R) (x : E),
      q338886_smul (a * b) x =
      q338886_smul a (q338886_smul b x);
  q338886_add_smul :
    forall (a b : R) (x : E),
      q338886_smul (a + b) x =
      q338886_add (q338886_smul a x) (q338886_smul b x);
  q338886_smul_add :
    forall (a : R) (x y : E),
      q338886_smul a (q338886_add x y) =
      q338886_add (q338886_smul a x) (q338886_smul a y);
  q338886_zero_smul :
    forall x : E, q338886_smul 0 x = q338886_zero;
  q338886_smul_zero :
    forall a : R, q338886_smul a q338886_zero = q338886_zero;
  q338886_norm_nonnegative :
    forall x : E, 0 <= q338886_norm x;
  q338886_norm_eq_zero :
    forall x : E,
      q338886_norm x = 0 <-> x = q338886_zero;
  q338886_norm_add_le :
    forall x y : E,
      q338886_norm (q338886_add x y) <=
      q338886_norm x + q338886_norm y;
  q338886_norm_smul :
    forall (a : R) (x : E),
      q338886_norm (q338886_smul a x) =
      Rabs a * q338886_norm x
}.

Arguments q338886_zero {E} _.
Arguments q338886_add {E} _ _ _.
Arguments q338886_neg {E} _ _.
Arguments q338886_smul {E} _ _ _.
Arguments q338886_norm {E} _ _.

Definition q338886_sub {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x y : E) : E :=
  q338886_add V x (q338886_neg V y).

Fixpoint q338886_list_map2 {A B C : Type}
    (operation : A -> B -> C)
    (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xt, y :: yt =>
      operation x y :: q338886_list_map2 operation xt yt
  | _, _ => []
  end.

Definition q338886_point_add (x y : list R) : list R :=
  q338886_list_map2 Rplus x y.

Definition q338886_point_neg (x : list R) : list R :=
  map Ropp x.

Definition q338886_point_sub (x y : list R) : list R :=
  q338886_point_add x (q338886_point_neg y).

Definition q338886_point_smul (a : R) (x : list R) : list R :=
  map (fun value => a * value) x.

Definition q338886_evector_add {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x y : list E) : list E :=
  q338886_list_map2 (q338886_add V) x y.

Definition q338886_evector_neg {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x : list E) : list E :=
  map (q338886_neg V) x.

Definition q338886_evector_sub {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x y : list E) : list E :=
  q338886_evector_add V x (q338886_evector_neg V y).

Definition q338886_evector_smul {E : Type}
    (V : q338886_normed_real_vector_space E)
    (a : R) (x : list E) : list E :=
  map (q338886_smul V a) x.

Fixpoint q338886_point_norm (x : list R) : R :=
  match x with
  | [] => 0
  | value :: tail =>
      Rmax (Rabs value) (q338886_point_norm tail)
  end.

Fixpoint q338886_evector_norm {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x : list E) : R :=
  match x with
  | [] => 0
  | value :: tail =>
      Rmax (q338886_norm V value)
        (q338886_evector_norm V tail)
  end.

Definition q338886_nth_evector {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x : list E) (i : nat) : E :=
  nth i x (q338886_zero V).

Fixpoint q338886_zero_point (dimension : nat) : list R :=
  match dimension with
  | O => []
  | S k => 0 :: q338886_zero_point k
  end.

Fixpoint q338886_basis_vector
    (dimension index : nat) : list R :=
  match dimension with
  | O => []
  | S k =>
      match index with
      | O => 1 :: q338886_zero_point k
      | S j => 0 :: q338886_basis_vector k j
      end
  end.

Fixpoint q338886_insert_coordinate
    (index : nat) (value : R) (x : list R) : list R :=
  match index, x with
  | O, _ => value :: x
  | S j, head :: tail =>
      head :: q338886_insert_coordinate j value tail
  | S _, [] => [value]
  end.

Fixpoint q338886_vector_sum {E : Type}
    (V : q338886_normed_real_vector_space E)
    (count : nat) (u : nat -> E) : E :=
  match count with
  | O => q338886_zero V
  | S k =>
      q338886_add V
        (q338886_vector_sum V k u) (u k)
  end.

Definition q338886_vector_sequence_converges {E : Type}
    (V : q338886_normed_real_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q338886_norm V
          (q338886_sub V (u n) limit) < epsilon.

Definition q338886_vector_sequence_cauchy {E : Type}
    (V : q338886_normed_real_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q338886_norm V
          (q338886_sub V (u m) (u n)) < epsilon.

Definition q338886_complete {E : Type}
    (V : q338886_normed_real_vector_space E) : Prop :=
  forall u : nat -> E,
    q338886_vector_sequence_cauchy V u ->
    exists limit : E,
      q338886_vector_sequence_converges V u limit.

Definition q338886_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Record q338886_continuous_linear_map
    (E : Type)
    (V : q338886_normed_real_vector_space E)
    (domain_dimension codomain_dimension : nat) : Type := {
  q338886_clm_apply : list R -> list E;
  q338886_clm_output_dimension :
    forall x : list R,
      q338886_valid_point domain_dimension x ->
      length (q338886_clm_apply x) = codomain_dimension;
  q338886_clm_add :
    forall x y : list R,
      q338886_valid_point domain_dimension x ->
      q338886_valid_point domain_dimension y ->
      q338886_clm_apply (q338886_point_add x y) =
      q338886_evector_add V
        (q338886_clm_apply x) (q338886_clm_apply y);
  q338886_clm_smul :
    forall (a : R) (x : list R),
      q338886_valid_point domain_dimension x ->
      q338886_clm_apply (q338886_point_smul a x) =
      q338886_evector_smul V a (q338886_clm_apply x);
  q338886_clm_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : list R,
        q338886_valid_point domain_dimension x ->
        q338886_evector_norm V (q338886_clm_apply x) <=
        bound * q338886_point_norm x
}.

Arguments q338886_clm_apply
  {E V domain_dimension codomain_dimension} _ _.

Definition q338886_countable
    (dimension : nat) (S : q338886_set (list R)) : Prop :=
  (forall x : list R, S x -> q338886_valid_point dimension x) /\
  exists encode : list R -> nat,
    forall x y : list R,
      S x ->
      S y ->
      encode x = encode y ->
      x = y.

Definition q338886_continuous_on {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (f : list R -> list E)
    (S : q338886_set (list R)) : Prop :=
  forall x : list R,
    S x ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : list R,
          S y ->
          q338886_point_norm
            (q338886_point_sub y x) < delta ->
          q338886_evector_norm V
            (q338886_evector_sub V (f y) (f x)) < epsilon.

Definition q338886_has_fderiv_at {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (f : list R -> list E)
    (derivative :
      @q338886_continuous_linear_map E V dimension dimension)
    (x : list R) : Prop :=
  q338886_valid_point dimension x /\
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall h : list R,
        q338886_valid_point dimension h ->
        q338886_point_norm h < delta ->
        q338886_evector_norm V
          (q338886_evector_sub V
            (q338886_evector_sub V
              (f (q338886_point_add x h)) (f x))
            (q338886_clm_apply derivative h))
        <= epsilon * q338886_point_norm h.

Definition q338886_almost_everywhere
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (P : list R -> Prop) : Prop :=
  exists null_set : q338886_set (list R),
    q338886_ennreal_eq
      (q338886_measure L null_set)
      q338886_ennreal_zero /\
    forall x : list R,
      q338886_valid_point dimension x ->
      ~ P x ->
      null_set x.

Definition q338886_finite_partition
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (k : nat)
    (cells : nat -> q338886_set (list R)) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q338886_measurable L (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q338886_disjoint (cells i) (cells j)) /\
  (forall x : list R,
    q338886_valid_point dimension x ->
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q338886_measurable_simple {E : Type}
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (s : list R -> E) : Prop :=
  exists (k : nat) (coefficients : nat -> E)
         (cells : nat -> q338886_set (list R)),
    @q338886_finite_partition dimension L k cells /\
    forall (x : list R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q338886_ae_strongly_measurable {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E) : Prop :=
  exists approximants : nat -> list R -> E,
    (forall n : nat,
      @q338886_measurable_simple E dimension L (approximants n)) /\
    @q338886_almost_everywhere dimension L
      (fun x =>
        q338886_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q338886_nonnegative_real : Type := {
  q338886_nnreal_value : R;
  q338886_nnreal_nonnegative : 0 <= q338886_nnreal_value
}.

Definition q338886_ennreal_of_nonnegative
    (x : q338886_nonnegative_real) : q338886_ennreal :=
  q338886_ennreal_finite (q338886_nnreal_value x).

Definition q338886_simple_lintegral_below
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> q338886_ennreal)
    (value : q338886_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q338886_nonnegative_real)
         (cells : nat -> q338886_set (list R)),
    @q338886_finite_partition dimension L k cells /\
    (forall (x : list R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q338886_ennreal_le
        (q338886_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q338886_ennreal_eq value
      (q338886_ennreal_partial_sum
        (fun i =>
          q338886_ennreal_mul
            (q338886_ennreal_of_nonnegative (coefficients i))
            (q338886_measure L (cells i)))
        k).

Definition q338886_lintegral_has_value
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> q338886_ennreal)
    (value : q338886_ennreal) : Prop :=
  q338886_ennreal_supremum
    (@q338886_simple_lintegral_below dimension L f) value.

Definition q338886_norm_ennreal {E : Type}
    (V : q338886_normed_real_vector_space E)
    (x : E) : q338886_ennreal :=
  q338886_ennreal_finite (q338886_norm V x).

Definition q338886_indicator {E : Type}
    (V : q338886_normed_real_vector_space E)
    (S : q338886_set (list R))
    (f : list R -> E)
    (x : list R) : E :=
  if excluded_middle_informative (S x)
  then f x
  else q338886_zero V.

Definition q338886_integrable {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E) : Prop :=
  @q338886_ae_strongly_measurable E V dimension L f /\
  exists value : q338886_ennreal,
    @q338886_lintegral_has_value dimension L
      (fun x => q338886_norm_ennreal V (f x)) value /\
    q338886_ennreal_finite_value value.

Definition q338886_integrable_on {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E)
    (S : q338886_set (list R)) : Prop :=
  @q338886_integrable E V dimension L
    (q338886_indicator V S f).

Definition q338886_weighted_cell_value {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (cell : q338886_set (list R))
    (coefficient value : E) : Prop :=
  (coefficient = q338886_zero V /\
    value = q338886_zero V) \/
  exists mass : R,
    q338886_ennreal_represents
      (q338886_measure L cell) mass /\
    value = q338886_smul V mass coefficient.

Definition q338886_simple_integral_has_value {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (s : list R -> E) (value : E) : Prop :=
  exists (k : nat) (coefficients terms : nat -> E)
         (cells : nat -> q338886_set (list R)),
    @q338886_finite_partition dimension L k cells /\
    (forall (x : list R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      @q338886_weighted_cell_value
        E V dimension L (cells i) (coefficients i) (terms i)) /\
    value = q338886_vector_sum V k terms.

Definition q338886_l1_approximates {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (approximants : nat -> list R -> E)
    (f : list R -> E) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q338886_ennreal,
        @q338886_lintegral_has_value dimension L
          (fun x =>
            q338886_norm_ennreal V
              (q338886_sub V (approximants n x) (f x)))
          integral_error /\
        q338886_ennreal_represents
          integral_error (errors n)) /\
    q338886_real_sequence_converges errors 0.

Definition q338886_standard_bochner_integral_value {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E) (value : E) : Prop :=
  exists (approximants : nat -> list R -> E)
         (integrals : nat -> E),
    (forall n : nat,
      @q338886_measurable_simple E dimension L (approximants n)) /\
    (forall n : nat,
      @q338886_simple_integral_has_value
        E V dimension L (approximants n) (integrals n)) /\
    @q338886_l1_approximates E V dimension L approximants f /\
    q338886_vector_sequence_converges V integrals value.

Definition q338886_bochner_integral {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E) : E :=
  match excluded_middle_informative
          (q338886_complete V /\
           exists value : E,
             @q338886_standard_bochner_integral_value
               E V dimension L f value) with
  | left _ =>
      epsilon (inhabits (q338886_zero V))
        (fun value : E =>
          @q338886_standard_bochner_integral_value
            E V dimension L f value)
  | right _ => q338886_zero V
  end.

Definition q338886_bochner_integral_on {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (L : q338886_lebesgue_measure_space dimension)
    (f : list R -> E)
    (S : q338886_set (list R)) : E :=
  @q338886_bochner_integral E V dimension L
    (q338886_indicator V S f).

Definition q338886_divergence {E : Type}
    (V : q338886_normed_real_vector_space E)
    (dimension : nat)
    (derivative :
      list R ->
      @q338886_continuous_linear_map E V dimension dimension)
    (x : list R) : E :=
  q338886_vector_sum V dimension
    (fun i =>
      q338886_nth_evector V
        (q338886_clm_apply (derivative x)
          (q338886_basis_vector dimension i))
        i).

Definition q338886_face_box
    (dimension : nat)
    (a b : list R)
    (index : nat) : q338886_set (list R) :=
  fun y =>
    q338886_valid_point dimension y /\
    q338886_box (S dimension) a b
      (q338886_insert_coordinate index
        (q338886_nth_real a index) y).

Definition q338886_front_face_value {E : Type}
    (V : q338886_normed_real_vector_space E)
    (f : list R -> list E)
    (b : list R)
    (index : nat)
    (y : list R) : E :=
  q338886_nth_evector V
    (f (q338886_insert_coordinate index
      (q338886_nth_real b index) y))
    index.

Definition q338886_back_face_value {E : Type}
    (V : q338886_normed_real_vector_space E)
    (f : list R -> list E)
    (a : list R)
    (index : nat)
    (y : list R) : E :=
  q338886_nth_evector V
    (f (q338886_insert_coordinate index
      (q338886_nth_real a index) y))
    index.

Theorem integral_divergence_of_hasFDerivAt_off_countable :
  forall (n : nat)
         (E : Type)
         (V : q338886_normed_real_vector_space E)
         (Lfull : q338886_lebesgue_measure_space (S n))
         (Lface : q338886_lebesgue_measure_space n)
         (a b : list R)
         (f : list R -> list E)
      (f' :
        list R ->
          @q338886_continuous_linear_map E V (S n) (S n))
         (s : q338886_set (list R)),
    q338886_valid_point (S n) a ->
    q338886_valid_point (S n) b ->
    (forall i : nat,
      (i < S n)%nat ->
      q338886_nth_real a i <= q338886_nth_real b i) ->
    (forall x : list R,
      q338886_valid_point (S n) x ->
      length (f x) = S n) ->
    q338886_countable (S n) s ->
    q338886_continuous_on V (S n) f
      (q338886_box (S n) a b) ->
    (forall x : list R,
      q338886_open_box (S n) a b x ->
      ~ s x ->
      @q338886_has_fderiv_at E V (S n) f (f' x) x) ->
    @q338886_integrable_on E V (S n) Lfull
      (@q338886_divergence E V (S n) f')
      (q338886_box (S n) a b) ->
    @q338886_bochner_integral_on E V (S n) Lfull
      (@q338886_divergence E V (S n) f')
      (q338886_box (S n) a b) =
    q338886_vector_sum V (S n)
      (fun i =>
        q338886_sub V
          (@q338886_bochner_integral_on E V n Lface
            (q338886_front_face_value V f b i)
            (q338886_face_box n a b i))
          (@q338886_bochner_integral_on E V n Lface
            (q338886_back_face_value V f a i)
            (q338886_face_box n a b i))).
Admitted.
