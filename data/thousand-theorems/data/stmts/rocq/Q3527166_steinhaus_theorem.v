(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527166
  (thousand-theorems__rocq__Q3527166), "Steinhaus theorem": in a locally
  compact topological group, the quotient of a positive-measure measurable
  set by itself is a neighborhood of the identity for an inner-regular Haar
  measure. This file contains no proof.
*)

From Stdlib Require Import List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3527166_set (A : Type) : Type := A -> Prop.

Definition q3527166_empty {A : Type} : q3527166_set A :=
  fun _ => False.

Definition q3527166_full {A : Type} : q3527166_set A :=
  fun _ => True.

Definition q3527166_complement {A : Type}
    (S : q3527166_set A) : q3527166_set A :=
  fun x => ~ S x.

Definition q3527166_countable_union {A : Type}
    (S : nat -> q3527166_set A) : q3527166_set A :=
  fun x => exists n : nat, S n x.

Definition q3527166_same_set {A : Type}
    (S T : q3527166_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q3527166_subset {A : Type}
    (S T : q3527166_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q3527166_disjoint {A : Type}
    (S T : q3527166_set A) : Prop :=
  forall x : A, ~ (S x /\ T x).

Definition q3527166_pairwise_disjoint {A : Type}
    (S : nat -> q3527166_set A) : Prop :=
  forall i j : nat,
    i <> j -> q3527166_disjoint (S i) (S j).

Record q3527166_group (G : Type) : Type := {
  q3527166_one : G;
  q3527166_mul : G -> G -> G;
  q3527166_inv : G -> G;
  q3527166_mul_assoc :
    forall x y z : G,
      q3527166_mul x (q3527166_mul y z) =
      q3527166_mul (q3527166_mul x y) z;
  q3527166_one_mul :
    forall x : G, q3527166_mul q3527166_one x = x;
  q3527166_mul_one :
    forall x : G, q3527166_mul x q3527166_one = x;
  q3527166_inv_mul :
    forall x : G,
      q3527166_mul (q3527166_inv x) x = q3527166_one;
  q3527166_mul_inv :
    forall x : G,
      q3527166_mul x (q3527166_inv x) = q3527166_one
}.

Arguments q3527166_one {G} _.
Arguments q3527166_mul {G} _ _ _.
Arguments q3527166_inv {G} _ _.

Record q3527166_topological_space (A : Type) : Type := {
  q3527166_is_open : q3527166_set (q3527166_set A);
  q3527166_open_extensional :
    forall U V : q3527166_set A,
      q3527166_same_set U V ->
      (q3527166_is_open U <-> q3527166_is_open V);
  q3527166_open_full :
    q3527166_is_open q3527166_full;
  q3527166_open_intersection :
    forall U V : q3527166_set A,
      q3527166_is_open U ->
      q3527166_is_open V ->
      q3527166_is_open (fun x => U x /\ V x);
  q3527166_open_union :
    forall family : q3527166_set (q3527166_set A),
      (forall U : q3527166_set A,
        family U -> q3527166_is_open U) ->
      q3527166_is_open
        (fun x =>
          exists U : q3527166_set A,
            family U /\ U x)
}.

Arguments q3527166_is_open {A} _ _.

Definition q3527166_neighborhood {A : Type}
    (T : q3527166_topological_space A)
    (x : A) (S : q3527166_set A) : Prop :=
  exists U : q3527166_set A,
    q3527166_is_open T U /\
    U x /\
    q3527166_subset U S.

Definition q3527166_is_topological_group {G : Type}
    (group : q3527166_group G)
    (T : q3527166_topological_space G) : Prop :=
  (forall (x y : G) (W : q3527166_set G),
      q3527166_is_open T W ->
      W (q3527166_mul group x y) ->
      exists U V : q3527166_set G,
        q3527166_is_open T U /\
        q3527166_is_open T V /\
        U x /\
        V y /\
        forall u v : G,
          U u ->
          V v ->
          W (q3527166_mul group u v)) /\
  forall (x : G) (W : q3527166_set G),
    q3527166_is_open T W ->
    W (q3527166_inv group x) ->
    exists U : q3527166_set G,
      q3527166_is_open T U /\
      U x /\
      forall u : G,
        U u -> W (q3527166_inv group u).

Definition q3527166_is_compact {A : Type}
    (T : q3527166_topological_space A)
    (K : q3527166_set A) : Prop :=
  forall cover : q3527166_set (q3527166_set A),
    (forall U : q3527166_set A,
      cover U -> q3527166_is_open T U) ->
    (forall x : A,
      K x ->
      exists U : q3527166_set A,
        cover U /\ U x) ->
    exists finite_cover : list (q3527166_set A),
      (forall U : q3527166_set A,
        In U finite_cover -> cover U) /\
      forall x : A,
        K x ->
        exists U : q3527166_set A,
          In U finite_cover /\ U x.

Definition q3527166_locally_compact {A : Type}
    (T : q3527166_topological_space A) : Prop :=
  forall (x : A) (N : q3527166_set A),
    q3527166_neighborhood T x N ->
    exists K : q3527166_set A,
      q3527166_neighborhood T x K /\
      q3527166_subset K N /\
      q3527166_is_compact T K.

Record q3527166_sigma_class (A : Type)
    (C : q3527166_set (q3527166_set A)) : Prop := {
  q3527166_sigma_extensional :
    forall S T : q3527166_set A,
      q3527166_same_set S T ->
      C S ->
      C T;
  q3527166_sigma_empty :
    C q3527166_empty;
  q3527166_sigma_complement :
    forall S : q3527166_set A,
      C S -> C (q3527166_complement S);
  q3527166_sigma_countable_union :
    forall S : nat -> q3527166_set A,
      (forall n : nat, C (S n)) ->
      C (q3527166_countable_union S)
}.

Definition q3527166_borel_set {A : Type}
    (T : q3527166_topological_space A)
    (S : q3527166_set A) : Prop :=
  forall C : q3527166_set (q3527166_set A),
    q3527166_sigma_class C ->
    (forall U : q3527166_set A,
      q3527166_is_open T U -> C U) ->
    C S.

Inductive q3527166_ennreal : Type :=
| q3527166_ennreal_finite :
    forall value : R, 0 <= value -> q3527166_ennreal
| q3527166_ennreal_infinity : q3527166_ennreal.

Arguments q3527166_ennreal_finite value nonnegative : clear implicits.

Definition q3527166_ennreal_zero : q3527166_ennreal :=
  q3527166_ennreal_finite 0 (Rle_refl 0).

Definition q3527166_ennreal_le
    (x y : q3527166_ennreal) : Prop :=
  match x, y with
  | q3527166_ennreal_finite a _,
    q3527166_ennreal_finite b _ => a <= b
  | q3527166_ennreal_finite _ _,
    q3527166_ennreal_infinity => True
  | q3527166_ennreal_infinity,
    q3527166_ennreal_finite _ _ => False
  | q3527166_ennreal_infinity,
    q3527166_ennreal_infinity => True
  end.

Definition q3527166_ennreal_lt
    (x y : q3527166_ennreal) : Prop :=
  match x, y with
  | q3527166_ennreal_finite a _,
    q3527166_ennreal_finite b _ => a < b
  | q3527166_ennreal_finite _ _,
    q3527166_ennreal_infinity => True
  | _, _ => False
  end.

Definition q3527166_ennreal_add
    (x y : q3527166_ennreal) : q3527166_ennreal :=
  match x, y with
  | q3527166_ennreal_finite a ha,
    q3527166_ennreal_finite b hb =>
      q3527166_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q3527166_ennreal_infinity
  end.

Fixpoint q3527166_ennreal_partial_sum
    (u : nat -> q3527166_ennreal)
    (n : nat) : q3527166_ennreal :=
  match n with
  | O => q3527166_ennreal_zero
  | S k =>
      q3527166_ennreal_add
        (q3527166_ennreal_partial_sum u k) (u k)
  end.

Definition q3527166_ennreal_supremum
    (values : q3527166_ennreal -> Prop)
    (bound : q3527166_ennreal) : Prop :=
  (forall value : q3527166_ennreal,
      values value ->
      q3527166_ennreal_le value bound) /\
  forall upper : q3527166_ennreal,
    (forall value : q3527166_ennreal,
      values value ->
      q3527166_ennreal_le value upper) ->
    q3527166_ennreal_le bound upper.

Definition q3527166_ennreal_infimum
    (values : q3527166_ennreal -> Prop)
    (bound : q3527166_ennreal) : Prop :=
  (forall value : q3527166_ennreal,
      values value ->
      q3527166_ennreal_le bound value) /\
  forall lower : q3527166_ennreal,
    (forall value : q3527166_ennreal,
      values value ->
      q3527166_ennreal_le lower value) ->
    q3527166_ennreal_le lower bound.

Definition q3527166_ennreal_series_sum
    (u : nat -> q3527166_ennreal)
    (sum : q3527166_ennreal) : Prop :=
  q3527166_ennreal_supremum
    (fun value =>
      exists n : nat,
        value = q3527166_ennreal_partial_sum u n)
    sum.

Record q3527166_measure {A : Type}
    (T : q3527166_topological_space A) : Type := {
  q3527166_measure_value :
    q3527166_set A -> q3527166_ennreal;
  q3527166_measure_extensional :
    forall S U : q3527166_set A,
      q3527166_same_set S U ->
      q3527166_measure_value S =
      q3527166_measure_value U;
  q3527166_measure_empty :
    q3527166_measure_value q3527166_empty =
    q3527166_ennreal_zero;
  q3527166_measure_monotone :
    forall S U : q3527166_set A,
      q3527166_subset S U ->
      q3527166_ennreal_le
        (q3527166_measure_value S)
        (q3527166_measure_value U);
  q3527166_measure_borel_trimmed :
    forall S : q3527166_set A,
      q3527166_ennreal_infimum
        (fun value =>
          exists U : q3527166_set A,
            q3527166_subset S U /\
            q3527166_borel_set T U /\
            value = q3527166_measure_value U)
        (q3527166_measure_value S);
  q3527166_measure_countable_subadditive :
    forall S : nat -> q3527166_set A,
      exists total : q3527166_ennreal,
        q3527166_ennreal_series_sum
          (fun n => q3527166_measure_value (S n))
          total /\
        q3527166_ennreal_le
          (q3527166_measure_value
            (q3527166_countable_union S))
          total;
  q3527166_measure_countable_additive :
    forall S : nat -> q3527166_set A,
      (forall n : nat, q3527166_borel_set T (S n)) ->
      q3527166_pairwise_disjoint S ->
      q3527166_ennreal_series_sum
        (fun n => q3527166_measure_value (S n))
        (q3527166_measure_value
          (q3527166_countable_union S))
}.

Arguments q3527166_measure_value {A T} _ _.

Record q3527166_is_haar_measure {G : Type}
    (group : q3527166_group G)
    (T : q3527166_topological_space G)
    (mu : q3527166_measure T) : Prop := {
  q3527166_haar_left_invariant :
    forall (g : G) (S : q3527166_set G),
      q3527166_borel_set T S ->
      q3527166_measure_value mu
        (fun x : G => S (q3527166_mul group g x)) =
      q3527166_measure_value mu S;
  q3527166_haar_finite_on_compact :
    forall K : q3527166_set G,
      q3527166_is_compact T K ->
      q3527166_ennreal_lt
        (q3527166_measure_value mu K)
        q3527166_ennreal_infinity;
  q3527166_haar_positive_on_nonempty_open :
    forall U : q3527166_set G,
      q3527166_is_open T U ->
      (exists x : G, U x) ->
      q3527166_measure_value mu U <>
      q3527166_ennreal_zero
}.

Definition q3527166_inner_regular {A : Type}
    (T : q3527166_topological_space A)
    (mu : q3527166_measure T) : Prop :=
  forall (S : q3527166_set A) (r : q3527166_ennreal),
    q3527166_borel_set T S ->
    q3527166_ennreal_lt r
      (q3527166_measure_value mu S) ->
    exists K : q3527166_set A,
      q3527166_subset K S /\
      q3527166_is_compact T K /\
      q3527166_ennreal_lt r
        (q3527166_measure_value mu K).

Definition q3527166_set_quotient {G : Type}
    (group : q3527166_group G)
    (S U : q3527166_set G) : q3527166_set G :=
  fun z =>
    exists x y : G,
      S x /\
      U y /\
      z = q3527166_mul group x (q3527166_inv group y).

Theorem MeasureTheory_Measure_div_mem_nhds_one_of_haar_pos :
  forall (G : Type)
         (group : q3527166_group G)
         (T : q3527166_topological_space G)
         (mu : q3527166_measure T)
         (E : q3527166_set G),
    @q3527166_is_topological_group G group T ->
    @q3527166_locally_compact G T ->
    @q3527166_is_haar_measure G group T mu ->
    @q3527166_inner_regular G T mu ->
    @q3527166_borel_set G T E ->
    q3527166_ennreal_lt q3527166_ennreal_zero
      (@q3527166_measure_value G T mu E) ->
    @q3527166_neighborhood G T
      (q3527166_one group)
      (@q3527166_set_quotient G group E E).
Admitted.
