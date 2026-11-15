(*
  Statement-only formalization of Thousand Theorems corpus artifact Q11352023
  (thousand-theorems__rocq__Q11352023), "Vitali convergence theorem":
  on an arbitrary measure space, convergence in measure together with uniform
  integrability and uniform tightness is equivalent to convergence in Lp for
  finite exponents p at least one. This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q11352023_set (A : Type) : Type := A -> Prop.

Definition q11352023_empty {A : Type} : q11352023_set A :=
  fun _ => False.

Definition q11352023_full {A : Type} : q11352023_set A :=
  fun _ => True.

Definition q11352023_complement {A : Type}
    (E : q11352023_set A) : q11352023_set A :=
  fun x => ~ E x.

Definition q11352023_countable_union {A : Type}
    (E : nat -> q11352023_set A) : q11352023_set A :=
  fun x => exists n : nat, E n x.

Definition q11352023_same_set {A : Type}
    (E F : q11352023_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q11352023_disjoint {A : Type}
    (E F : q11352023_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q11352023_pairwise_disjoint {A : Type}
    (E : nat -> q11352023_set A) : Prop :=
  forall i j : nat, i <> j -> q11352023_disjoint (E i) (E j).

Inductive q11352023_ennreal : Type :=
| q11352023_ennreal_finite :
    forall value : R, 0 <= value -> q11352023_ennreal
| q11352023_ennreal_infinity : q11352023_ennreal.

Arguments q11352023_ennreal_finite value nonnegative : clear implicits.

Definition q11352023_ennreal_zero : q11352023_ennreal :=
  q11352023_ennreal_finite 0 (Rle_refl 0).

Definition q11352023_ennreal_one : q11352023_ennreal :=
  q11352023_ennreal_finite 1 Rle_0_1.

Definition q11352023_ennreal_eq
    (x y : q11352023_ennreal) : Prop :=
  match x, y with
  | q11352023_ennreal_finite a _,
    q11352023_ennreal_finite b _ => a = b
  | q11352023_ennreal_infinity,
    q11352023_ennreal_infinity => True
  | _, _ => False
  end.

Definition q11352023_ennreal_le
    (x y : q11352023_ennreal) : Prop :=
  match x, y with
  | q11352023_ennreal_finite a _,
    q11352023_ennreal_finite b _ => a <= b
  | q11352023_ennreal_finite _ _,
    q11352023_ennreal_infinity => True
  | q11352023_ennreal_infinity,
    q11352023_ennreal_finite _ _ => False
  | q11352023_ennreal_infinity,
    q11352023_ennreal_infinity => True
  end.

Definition q11352023_ennreal_lt
    (x y : q11352023_ennreal) : Prop :=
  match x, y with
  | q11352023_ennreal_finite a _,
    q11352023_ennreal_finite b _ => a < b
  | q11352023_ennreal_finite _ _,
    q11352023_ennreal_infinity => True
  | _, _ => False
  end.

Definition q11352023_ennreal_below_real
    (x : q11352023_ennreal) (bound : R) : Prop :=
  match x with
  | q11352023_ennreal_finite value _ => value < bound
  | q11352023_ennreal_infinity => False
  end.

Definition q11352023_ennreal_le_real
    (x : q11352023_ennreal) (bound : R) : Prop :=
  match x with
  | q11352023_ennreal_finite value _ => value <= bound
  | q11352023_ennreal_infinity => False
  end.

Definition q11352023_ennreal_add
    (x y : q11352023_ennreal) : q11352023_ennreal :=
  match x, y with
  | q11352023_ennreal_finite a ha,
    q11352023_ennreal_finite b hb =>
      q11352023_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q11352023_ennreal_infinity
  end.

Definition q11352023_ennreal_mul
    (x y : q11352023_ennreal) : q11352023_ennreal :=
  match x, y with
  | q11352023_ennreal_finite a ha,
    q11352023_ennreal_finite b hb =>
      q11352023_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q11352023_ennreal_finite a _, q11352023_ennreal_infinity
  | q11352023_ennreal_infinity, q11352023_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q11352023_ennreal_zero
      else q11352023_ennreal_infinity
  | q11352023_ennreal_infinity, q11352023_ennreal_infinity =>
      q11352023_ennreal_infinity
  end.

Definition q11352023_ennreal_rpow
    (x : q11352023_ennreal) (exponent : R) : q11352023_ennreal :=
  match x with
  | q11352023_ennreal_finite value _ =>
      if Req_EM_T value 0 then
        if Rlt_dec 0 exponent then q11352023_ennreal_zero
        else if Req_EM_T exponent 0
             then q11352023_ennreal_one
             else q11352023_ennreal_infinity
      else
        q11352023_ennreal_finite
          (exp (ln value * exponent))
          (Rlt_le 0 (exp (ln value * exponent))
            (exp_pos (ln value * exponent)))
  | q11352023_ennreal_infinity =>
      if Rlt_dec 0 exponent then q11352023_ennreal_infinity
      else if Req_EM_T exponent 0
           then q11352023_ennreal_one
           else q11352023_ennreal_zero
  end.

Fixpoint q11352023_ennreal_partial_sum
    (u : nat -> q11352023_ennreal)
    (n : nat) : q11352023_ennreal :=
  match n with
  | O => q11352023_ennreal_zero
  | S k =>
      q11352023_ennreal_add
        (q11352023_ennreal_partial_sum u k) (u k)
  end.

Definition q11352023_ennreal_supremum
    (values : q11352023_ennreal -> Prop)
    (bound : q11352023_ennreal) : Prop :=
  (forall value : q11352023_ennreal,
      values value -> q11352023_ennreal_le value bound) /\
  (forall upper : q11352023_ennreal,
      (forall value : q11352023_ennreal,
        values value -> q11352023_ennreal_le value upper) ->
      q11352023_ennreal_le bound upper).

Definition q11352023_ennreal_infimum
    (values : q11352023_ennreal -> Prop)
    (bound : q11352023_ennreal) : Prop :=
  (forall value : q11352023_ennreal,
      values value -> q11352023_ennreal_le bound value) /\
  (forall lower : q11352023_ennreal,
      (forall value : q11352023_ennreal,
        values value -> q11352023_ennreal_le lower value) ->
      q11352023_ennreal_le lower bound).

Definition q11352023_ennreal_series_sum
    (u : nat -> q11352023_ennreal)
    (sum : q11352023_ennreal) : Prop :=
  q11352023_ennreal_supremum
    (fun value =>
      exists n : nat,
        q11352023_ennreal_eq value
          (q11352023_ennreal_partial_sum u n))
    sum.

Record q11352023_measure_space (A : Type) : Type := {
  q11352023_measurable : q11352023_set A -> Prop;
  q11352023_measurable_extensional :
    forall E F : q11352023_set A,
      q11352023_same_set E F ->
      (q11352023_measurable E <-> q11352023_measurable F);
  q11352023_measurable_empty :
    q11352023_measurable q11352023_empty;
  q11352023_measurable_complement :
    forall E : q11352023_set A,
      q11352023_measurable E ->
      q11352023_measurable (q11352023_complement E);
  q11352023_measurable_countable_union :
    forall E : nat -> q11352023_set A,
      (forall n : nat, q11352023_measurable (E n)) ->
      q11352023_measurable (q11352023_countable_union E);
  q11352023_measure : q11352023_set A -> q11352023_ennreal;
  q11352023_measure_extensional :
    forall E F : q11352023_set A,
      q11352023_same_set E F ->
      q11352023_ennreal_eq
        (q11352023_measure E) (q11352023_measure F);
  q11352023_measure_empty :
    q11352023_ennreal_eq
      (q11352023_measure q11352023_empty)
      q11352023_ennreal_zero;
  q11352023_measure_monotone :
    forall E F : q11352023_set A,
      (forall x : A, E x -> F x) ->
      q11352023_ennreal_le
        (q11352023_measure E) (q11352023_measure F);
  q11352023_measure_trimmed :
    forall E : q11352023_set A,
      q11352023_ennreal_infimum
        (fun value =>
          exists F : q11352023_set A,
            q11352023_measurable F /\
            (forall x : A, E x -> F x) /\
            q11352023_ennreal_eq
              value (q11352023_measure F))
        (q11352023_measure E);
  q11352023_measure_countable_subadditive :
    forall E : nat -> q11352023_set A,
      exists total : q11352023_ennreal,
        q11352023_ennreal_series_sum
          (fun n => q11352023_measure (E n)) total /\
        q11352023_ennreal_le
          (q11352023_measure (q11352023_countable_union E))
          total;
  q11352023_measure_countable_additive :
    forall E : nat -> q11352023_set A,
      (forall n : nat, q11352023_measurable (E n)) ->
      q11352023_pairwise_disjoint E ->
      q11352023_ennreal_series_sum
        (fun n => q11352023_measure (E n))
        (q11352023_measure (q11352023_countable_union E))
}.

Arguments q11352023_measurable {A} _ _.
Arguments q11352023_measure {A} _ _.

Definition q11352023_almost_everywhere {A : Type}
    (mu : q11352023_measure_space A)
    (P : A -> Prop) : Prop :=
  q11352023_ennreal_eq
    (q11352023_measure mu (fun x => ~ P x))
    q11352023_ennreal_zero.

Record q11352023_normed_add_comm_group (G : Type) : Type := {
  q11352023_zero : G;
  q11352023_add : G -> G -> G;
  q11352023_neg : G -> G;
  q11352023_norm : G -> R;
  q11352023_add_assoc :
    forall x y z : G,
      q11352023_add x (q11352023_add y z) =
      q11352023_add (q11352023_add x y) z;
  q11352023_add_comm :
    forall x y : G, q11352023_add x y = q11352023_add y x;
  q11352023_add_zero :
    forall x : G, q11352023_add x q11352023_zero = x;
  q11352023_add_neg :
    forall x : G,
      q11352023_add x (q11352023_neg x) = q11352023_zero;
  q11352023_norm_nonnegative :
    forall x : G, 0 <= q11352023_norm x;
  q11352023_norm_eq_zero :
    forall x : G,
      q11352023_norm x = 0 <-> x = q11352023_zero;
  q11352023_norm_neg :
    forall x : G,
      q11352023_norm (q11352023_neg x) = q11352023_norm x;
  q11352023_norm_add_le :
    forall x y : G,
      q11352023_norm (q11352023_add x y) <=
      q11352023_norm x + q11352023_norm y
}.

Arguments q11352023_zero {G} _.
Arguments q11352023_add {G} _ _ _.
Arguments q11352023_neg {G} _ _.
Arguments q11352023_norm {G} _ _.

Definition q11352023_sub {G : Type}
    (V : q11352023_normed_add_comm_group G)
    (x y : G) : G :=
  q11352023_add V x (q11352023_neg V y).

Definition q11352023_vector_sequence_converges {G : Type}
    (V : q11352023_normed_add_comm_group G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q11352023_norm V
          (q11352023_sub V (u n) limit) < epsilon.

Definition q11352023_finite_partition {A : Type}
    (mu : q11352023_measure_space A)
    (k : nat) (cells : nat -> q11352023_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q11352023_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q11352023_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q11352023_measurable_simple {A G : Type}
    (mu : q11352023_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q11352023_set A),
    q11352023_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q11352023_ae_strongly_measurable {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q11352023_measurable_simple mu (approximants n)) /\
    q11352023_almost_everywhere mu
      (fun x =>
        q11352023_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q11352023_nonnegative_real : Type := {
  q11352023_nnreal_value : R;
  q11352023_nnreal_nonnegative : 0 <= q11352023_nnreal_value
}.

Definition q11352023_ennreal_of_nonnegative
    (x : q11352023_nonnegative_real) : q11352023_ennreal :=
  q11352023_ennreal_finite
    (q11352023_nnreal_value x)
    (q11352023_nnreal_nonnegative x).

Definition q11352023_simple_lintegral_below {A : Type}
    (mu : q11352023_measure_space A)
    (f : A -> q11352023_ennreal)
    (value : q11352023_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q11352023_nonnegative_real)
         (cells : nat -> q11352023_set A),
    q11352023_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q11352023_ennreal_le
        (q11352023_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q11352023_ennreal_eq value
      (q11352023_ennreal_partial_sum
        (fun i =>
          q11352023_ennreal_mul
            (q11352023_ennreal_of_nonnegative (coefficients i))
            (q11352023_measure mu (cells i)))
        k).

Definition q11352023_lintegral_has_value {A : Type}
    (mu : q11352023_measure_space A)
    (f : A -> q11352023_ennreal)
    (value : q11352023_ennreal) : Prop :=
  q11352023_ennreal_supremum
    (q11352023_simple_lintegral_below mu f) value.

Definition q11352023_norm_rpow {G : Type}
    (V : q11352023_normed_add_comm_group G)
    (x : G) (exponent : R) : q11352023_ennreal :=
  q11352023_ennreal_rpow
    (q11352023_ennreal_finite
      (q11352023_norm V x)
      (q11352023_norm_nonnegative V x))
    exponent.

Definition q11352023_eLpNorm_has_value {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : A -> G)
    (p value : q11352023_ennreal) : Prop :=
  match p with
  | q11352023_ennreal_finite exponent _ =>
      0 < exponent /\
      exists integral : q11352023_ennreal,
        q11352023_lintegral_has_value mu
          (fun x => q11352023_norm_rpow V (f x) exponent)
          integral /\
        q11352023_ennreal_eq value
          (q11352023_ennreal_rpow integral (/ exponent))
  | q11352023_ennreal_infinity => False
  end.

Definition q11352023_mem_lp {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : A -> G)
    (p : q11352023_ennreal) : Prop :=
  q11352023_ae_strongly_measurable V mu f /\
  exists value : q11352023_ennreal,
    q11352023_eLpNorm_has_value V mu f p value /\
    q11352023_ennreal_lt value q11352023_ennreal_infinity.

Definition q11352023_indicator {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (E : q11352023_set A)
    (f : A -> G) (x : A) : G :=
  if excluded_middle_informative (E x)
  then f x
  else q11352023_zero V.

Definition q11352023_tendsto_in_measure {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : nat -> A -> G)
    (g : A -> G) : Prop :=
  forall epsilon delta : R,
    0 < epsilon ->
    0 < delta ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q11352023_ennreal_below_real
          (q11352023_measure mu
            (fun x =>
              epsilon <=
              q11352023_norm V
                (q11352023_sub V (f n x) (g x))))
          delta.

Definition q11352023_unif_integrable {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : nat -> A -> G)
    (p : q11352023_ennreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall (n : nat) (E : q11352023_set A),
        q11352023_measurable mu E ->
        q11352023_ennreal_le_real
          (q11352023_measure mu E) delta ->
        exists value : q11352023_ennreal,
          q11352023_eLpNorm_has_value V mu
            (q11352023_indicator V E (f n)) p value /\
          q11352023_ennreal_le_real value epsilon.

Definition q11352023_unif_tight {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : nat -> A -> G)
    (p : q11352023_ennreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists E : q11352023_set A,
      ~ q11352023_ennreal_eq
          (q11352023_measure mu E)
          q11352023_ennreal_infinity /\
      forall n : nat,
        exists value : q11352023_ennreal,
          q11352023_eLpNorm_has_value V mu
            (q11352023_indicator V
              (q11352023_complement E) (f n))
            p value /\
          q11352023_ennreal_le_real value epsilon.

Definition q11352023_tendsto_lp {A G : Type}
    (V : q11352023_normed_add_comm_group G)
    (mu : q11352023_measure_space A)
    (f : nat -> A -> G)
    (g : A -> G)
    (p : q11352023_ennreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        exists value : q11352023_ennreal,
          q11352023_eLpNorm_has_value V mu
            (fun x => q11352023_sub V (f n x) (g x))
            p value /\
          q11352023_ennreal_below_real value epsilon.

Theorem tendstoInMeasure_iff_tendsto_Lp :
  forall (Alpha G : Type)
         (V : q11352023_normed_add_comm_group G)
         (mu : q11352023_measure_space Alpha)
         (p : q11352023_ennreal)
         (f : nat -> Alpha -> G)
         (g : Alpha -> G),
    q11352023_ennreal_le q11352023_ennreal_one p ->
    p <> q11352023_ennreal_infinity ->
    (forall n : nat, q11352023_mem_lp V mu (f n) p) ->
    q11352023_mem_lp V mu g p ->
    (q11352023_tendsto_in_measure V mu f g /\
     q11352023_unif_integrable V mu f p /\
     q11352023_unif_tight V mu f p
     <->
     q11352023_tendsto_lp V mu f g p).
Admitted.
