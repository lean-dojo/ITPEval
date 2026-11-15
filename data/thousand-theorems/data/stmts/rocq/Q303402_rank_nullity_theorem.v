(*
  Statement-only formalization of Thousand Theorems corpus artifact Q303402
  (thousand-theorems__rocq__Q303402), "Rank-nullity theorem": for a linear
  map of modules over a ring satisfying the rank-nullity property, the
  cardinal rank of its range plus that of its kernel equals the rank of its
  domain. This file contains no proof.
*)

From Stdlib Require Import List.

Import ListNotations.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q303402_ring : Type := {
  q303402_ring_carrier : Type;
  q303402_zero : q303402_ring_carrier;
  q303402_one : q303402_ring_carrier;
  q303402_add :
    q303402_ring_carrier ->
    q303402_ring_carrier ->
    q303402_ring_carrier;
  q303402_mul :
    q303402_ring_carrier ->
    q303402_ring_carrier ->
    q303402_ring_carrier;
  q303402_neg :
    q303402_ring_carrier -> q303402_ring_carrier;
  q303402_add_assoc :
    forall x y z : q303402_ring_carrier,
      q303402_add x (q303402_add y z) =
      q303402_add (q303402_add x y) z;
  q303402_add_comm :
    forall x y : q303402_ring_carrier,
      q303402_add x y = q303402_add y x;
  q303402_zero_add :
    forall x : q303402_ring_carrier,
      q303402_add q303402_zero x = x;
  q303402_add_zero :
    forall x : q303402_ring_carrier,
      q303402_add x q303402_zero = x;
  q303402_neg_add :
    forall x : q303402_ring_carrier,
      q303402_add (q303402_neg x) x = q303402_zero;
  q303402_add_neg :
    forall x : q303402_ring_carrier,
      q303402_add x (q303402_neg x) = q303402_zero;
  q303402_mul_assoc :
    forall x y z : q303402_ring_carrier,
      q303402_mul x (q303402_mul y z) =
      q303402_mul (q303402_mul x y) z;
  q303402_one_mul :
    forall x : q303402_ring_carrier,
      q303402_mul q303402_one x = x;
  q303402_mul_one :
    forall x : q303402_ring_carrier,
      q303402_mul x q303402_one = x;
  q303402_mul_add :
    forall x y z : q303402_ring_carrier,
      q303402_mul x (q303402_add y z) =
      q303402_add
        (q303402_mul x y) (q303402_mul x z);
  q303402_add_mul :
    forall x y z : q303402_ring_carrier,
      q303402_mul (q303402_add x y) z =
      q303402_add
        (q303402_mul x z) (q303402_mul y z)
}.

Arguments q303402_ring_carrier _ : clear implicits.

Record q303402_module (R : q303402_ring) : Type := {
  q303402_module_carrier : Type;
  q303402_mzero : q303402_module_carrier;
  q303402_madd :
    q303402_module_carrier ->
    q303402_module_carrier ->
    q303402_module_carrier;
  q303402_mneg :
    q303402_module_carrier -> q303402_module_carrier;
  q303402_smul :
    q303402_ring_carrier R ->
    q303402_module_carrier ->
    q303402_module_carrier;
  q303402_madd_assoc :
    forall x y z : q303402_module_carrier,
      q303402_madd x (q303402_madd y z) =
      q303402_madd (q303402_madd x y) z;
  q303402_madd_comm :
    forall x y : q303402_module_carrier,
      q303402_madd x y = q303402_madd y x;
  q303402_mzero_add :
    forall x : q303402_module_carrier,
      q303402_madd q303402_mzero x = x;
  q303402_madd_zero :
    forall x : q303402_module_carrier,
      q303402_madd x q303402_mzero = x;
  q303402_mneg_add :
    forall x : q303402_module_carrier,
      q303402_madd (q303402_mneg x) x = q303402_mzero;
  q303402_madd_neg :
    forall x : q303402_module_carrier,
      q303402_madd x (q303402_mneg x) = q303402_mzero;
  q303402_one_smul :
    forall x : q303402_module_carrier,
      q303402_smul (q303402_one R) x = x;
  q303402_mul_smul :
    forall (r s : q303402_ring_carrier R)
           (x : q303402_module_carrier),
      q303402_smul (q303402_mul R r s) x =
      q303402_smul r (q303402_smul s x);
  q303402_add_smul :
    forall (r s : q303402_ring_carrier R)
           (x : q303402_module_carrier),
      q303402_smul (q303402_add R r s) x =
      q303402_madd
        (q303402_smul r x) (q303402_smul s x);
  q303402_smul_add :
    forall (r : q303402_ring_carrier R)
           (x y : q303402_module_carrier),
      q303402_smul r (q303402_madd x y) =
      q303402_madd
        (q303402_smul r x) (q303402_smul r y);
  q303402_zero_smul :
    forall x : q303402_module_carrier,
      q303402_smul (q303402_zero R) x = q303402_mzero;
  q303402_smul_zero :
    forall r : q303402_ring_carrier R,
      q303402_smul r q303402_mzero = q303402_mzero
}.

Arguments q303402_module_carrier {R} _.
Arguments q303402_mzero {R} _.
Arguments q303402_madd {R} _ _ _.
Arguments q303402_mneg {R} _ _.
Arguments q303402_smul {R} _ _ _.

Record q303402_linear_map
    {R : q303402_ring}
    (M N : q303402_module R) : Type := {
  q303402_linear_apply :
    q303402_module_carrier M ->
    q303402_module_carrier N;
  q303402_linear_map_add :
    forall x y : q303402_module_carrier M,
      q303402_linear_apply (q303402_madd M x y) =
      q303402_madd N
        (q303402_linear_apply x) (q303402_linear_apply y);
  q303402_linear_map_smul :
    forall (r : q303402_ring_carrier R)
           (x : q303402_module_carrier M),
      q303402_linear_apply (q303402_smul M r x) =
      q303402_smul N r (q303402_linear_apply x)
}.

Arguments q303402_linear_apply {R M N} _ _.

Fixpoint q303402_linear_combination
    {R : q303402_ring}
    (M : q303402_module R)
    {I : Type}
    (vectors : I -> q303402_module_carrier M)
    (terms : list (I * q303402_ring_carrier R)) :
    q303402_module_carrier M :=
  match terms with
  | [] => q303402_mzero M
  | (i, r) :: rest =>
      q303402_madd M
        (q303402_smul M r (vectors i))
        (q303402_linear_combination M vectors rest)
  end.

Definition q303402_linearly_independent
    {R : q303402_ring}
    (M : q303402_module R)
    {I : Type}
    (vectors : I -> q303402_module_carrier M) : Prop :=
  forall terms : list (I * q303402_ring_carrier R),
    NoDup (map (@fst I (q303402_ring_carrier R)) terms) ->
    q303402_linear_combination M vectors terms =
      q303402_mzero M ->
    Forall
      (fun term => snd term = q303402_zero R)
      terms.

Definition q303402_is_submodule
    {R : q303402_ring}
    (M : q303402_module R)
    (S : q303402_module_carrier M -> Prop) : Prop :=
  S (q303402_mzero M) /\
  (forall x y : q303402_module_carrier M,
      S x -> S y -> S (q303402_madd M x y)) /\
  (forall x : q303402_module_carrier M,
      S x -> S (q303402_mneg M x)) /\
  (forall (r : q303402_ring_carrier R)
          (x : q303402_module_carrier M),
      S x -> S (q303402_smul M r x)).

Definition q303402_submodule_linearly_independent
    {R : q303402_ring}
    (M : q303402_module R)
    (S : q303402_module_carrier M -> Prop)
    {I : Type}
    (vectors : I -> q303402_module_carrier M) : Prop :=
  (forall i : I, S (vectors i)) /\
  q303402_linearly_independent M vectors.

Definition q303402_quotient_linearly_independent
    {R : q303402_ring}
    (M : q303402_module R)
    (S : q303402_module_carrier M -> Prop)
    {I : Type}
    (representatives : I -> q303402_module_carrier M) : Prop :=
  forall terms : list (I * q303402_ring_carrier R),
    NoDup (map (@fst I (q303402_ring_carrier R)) terms) ->
    S (q303402_linear_combination M representatives terms) ->
    Forall
      (fun term => snd term = q303402_zero R)
      terms.

Definition q303402_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q303402_same_cardinality (A B : Type) : Prop :=
  exists forward : A -> B,
    q303402_injective forward /\
    forall y : B, exists x : A, forward x = y.

Record q303402_rank_representation
    {R : q303402_ring}
    (M : q303402_module R) : Type := {
  q303402_rank_index : Type;
  q303402_rank_vectors :
    q303402_rank_index -> q303402_module_carrier M;
  q303402_rank_independent :
    q303402_linearly_independent M q303402_rank_vectors;
  q303402_rank_dominates :
    forall (J : Type)
           (vectors : J -> q303402_module_carrier M),
      q303402_linearly_independent M vectors ->
      exists injection : J -> q303402_rank_index,
        q303402_injective injection
}.

Arguments q303402_rank_index {R M} _.

Record q303402_submodule_rank_representation
    {R : q303402_ring}
    (M : q303402_module R)
    (S : q303402_module_carrier M -> Prop) : Type := {
  q303402_submodule_rank_index : Type;
  q303402_submodule_rank_vectors :
    q303402_submodule_rank_index ->
    q303402_module_carrier M;
  q303402_submodule_rank_independent :
    q303402_submodule_linearly_independent
      M S q303402_submodule_rank_vectors;
  q303402_submodule_rank_dominates :
    forall (J : Type)
           (vectors : J -> q303402_module_carrier M),
      q303402_submodule_linearly_independent M S vectors ->
      exists injection : J -> q303402_submodule_rank_index,
        q303402_injective injection
}.

Arguments q303402_submodule_rank_index {R M S} _.

Record q303402_quotient_rank_representation
    {R : q303402_ring}
    (M : q303402_module R)
    (S : q303402_module_carrier M -> Prop) : Type := {
  q303402_quotient_rank_index : Type;
  q303402_quotient_rank_representatives :
    q303402_quotient_rank_index ->
    q303402_module_carrier M;
  q303402_quotient_rank_independent :
    q303402_quotient_linearly_independent
      M S q303402_quotient_rank_representatives;
  q303402_quotient_rank_dominates :
    forall (J : Type)
           (representatives : J -> q303402_module_carrier M),
      q303402_quotient_linearly_independent
        M S representatives ->
      exists injection : J -> q303402_quotient_rank_index,
        q303402_injective injection
}.

Arguments q303402_quotient_rank_index {R M S} _.

Record q303402_has_rank_nullity (R : q303402_ring) : Prop := {
  q303402_rank_attained :
    forall M : q303402_module R,
      exists rank : q303402_rank_representation M, True;
  q303402_submodule_rank_attained :
    forall (M : q303402_module R)
           (S : q303402_module_carrier M -> Prop),
      q303402_is_submodule M S ->
      exists rank :
        q303402_submodule_rank_representation M S, True;
  q303402_quotient_rank_attained :
    forall (M : q303402_module R)
           (S : q303402_module_carrier M -> Prop),
      q303402_is_submodule M S ->
      exists rank :
        q303402_quotient_rank_representation M S, True;
  q303402_rank_quotient_add_rank :
    forall (M : q303402_module R)
           (S : q303402_module_carrier M -> Prop),
      q303402_is_submodule M S ->
      forall
        (quotient_rank :
          q303402_quotient_rank_representation M S)
        (submodule_rank :
          q303402_submodule_rank_representation M S)
        (module_rank : q303402_rank_representation M),
        q303402_same_cardinality
          ((q303402_quotient_rank_index quotient_rank +
            q303402_submodule_rank_index submodule_rank)%type)
          (q303402_rank_index module_rank)
}.

Definition q303402_kernel
    {R : q303402_ring}
    {M N : q303402_module R}
    (f : q303402_linear_map M N) :
    q303402_module_carrier M -> Prop :=
  fun x =>
    q303402_linear_apply f x = q303402_mzero N.

Definition q303402_range
    {R : q303402_ring}
    {M N : q303402_module R}
    (f : q303402_linear_map M N) :
    q303402_module_carrier N -> Prop :=
  fun y =>
    exists x : q303402_module_carrier M,
      q303402_linear_apply f x = y.

Definition q303402_rank_range_add_rank_ker
    {R : q303402_ring}
    {M N : q303402_module R}
    (f : q303402_linear_map M N) : Prop :=
  forall
    (range_rank :
      q303402_submodule_rank_representation
        N (q303402_range f))
    (kernel_rank :
      q303402_submodule_rank_representation
        M (q303402_kernel f))
    (domain_rank : q303402_rank_representation M),
    q303402_same_cardinality
      ((q303402_submodule_rank_index range_rank +
        q303402_submodule_rank_index kernel_rank)%type)
      (q303402_rank_index domain_rank).

Theorem LinearMap_rank_range_add_rank_ker :
  forall (R : q303402_ring)
         (M M1 : q303402_module R)
         (f : q303402_linear_map M M1),
    q303402_has_rank_nullity R ->
    q303402_rank_range_add_rank_ker f.
Admitted.
