(*
  Statement-only formalization of Thousand Theorems corpus artifact Q193878
  (thousand-theorems__rocq__Q193878), "Chinese remainder theorem": for a
  finite family of pairwise comaximal ideals in a commutative ring, the
  quotient by their intersection is canonically isomorphic to the product of
  the quotient rings. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q193878_commutative_ring (R : Type) : Type := {
  q193878_zero : R;
  q193878_one : R;
  q193878_add : R -> R -> R;
  q193878_mul : R -> R -> R;
  q193878_neg : R -> R;
  q193878_add_assoc :
    forall x y z : R,
      q193878_add x (q193878_add y z) =
      q193878_add (q193878_add x y) z;
  q193878_add_comm :
    forall x y : R, q193878_add x y = q193878_add y x;
  q193878_add_zero :
    forall x : R, q193878_add x q193878_zero = x;
  q193878_add_neg :
    forall x : R, q193878_add x (q193878_neg x) = q193878_zero;
  q193878_mul_assoc :
    forall x y z : R,
      q193878_mul x (q193878_mul y z) =
      q193878_mul (q193878_mul x y) z;
  q193878_mul_comm :
    forall x y : R, q193878_mul x y = q193878_mul y x;
  q193878_mul_one :
    forall x : R, q193878_mul x q193878_one = x;
  q193878_left_distrib :
    forall x y z : R,
      q193878_mul x (q193878_add y z) =
      q193878_add (q193878_mul x y) (q193878_mul x z)
}.

Arguments q193878_zero {R} _.
Arguments q193878_one {R} _.
Arguments q193878_add {R} _ _ _.
Arguments q193878_mul {R} _ _ _.
Arguments q193878_neg {R} _ _.

Definition q193878_sub
    {R : Type} (CR : q193878_commutative_ring R)
    (x y : R) : R :=
  q193878_add CR x (q193878_neg CR y).

Record q193878_ideal
    (R : Type) (CR : q193878_commutative_ring R) : Type := {
  q193878_ideal_mem : R -> Prop;
  q193878_ideal_zero :
    q193878_ideal_mem (q193878_zero CR);
  q193878_ideal_add :
    forall x y : R,
      q193878_ideal_mem x ->
      q193878_ideal_mem y ->
      q193878_ideal_mem (q193878_add CR x y);
  q193878_ideal_neg :
    forall x : R,
      q193878_ideal_mem x ->
      q193878_ideal_mem (q193878_neg CR x);
  q193878_ideal_mul :
    forall a x : R,
      q193878_ideal_mem x ->
      q193878_ideal_mem (q193878_mul CR a x)
}.

Arguments q193878_ideal_mem {R CR} _ _.

Definition q193878_is_finite (index : Type) : Prop :=
  exists enumeration : list index,
    forall i : index, In i enumeration.

Definition q193878_ideals_comaximal
    {R : Type}
    {CR : q193878_commutative_ring R}
    (I J : @q193878_ideal R CR) : Prop :=
  exists x y : R,
    q193878_ideal_mem I x /\
    q193878_ideal_mem J y /\
    q193878_add CR x y = q193878_one CR.

Definition q193878_pairwise_comaximal
    {R index : Type}
    {CR : q193878_commutative_ring R}
    (ideals : index -> @q193878_ideal R CR) : Prop :=
  forall i j : index,
    i <> j ->
    q193878_ideals_comaximal (ideals i) (ideals j).

Definition q193878_ideal_quotient_equal
    {R : Type}
    {CR : q193878_commutative_ring R}
    (I : @q193878_ideal R CR)
    (x y : R) : Prop :=
  q193878_ideal_mem I (q193878_sub CR x y).

Definition q193878_intersection_quotient_equal
    {R index : Type}
    {CR : q193878_commutative_ring R}
    (ideals : index -> @q193878_ideal R CR)
    (x y : R) : Prop :=
  forall i : index,
    q193878_ideal_quotient_equal (ideals i) x y.

Definition q193878_product_quotient_equal
    {R index : Type}
    {CR : q193878_commutative_ring R}
    (ideals : index -> @q193878_ideal R CR)
    (x y : index -> R) : Prop :=
  forall i : index,
    q193878_ideal_quotient_equal (ideals i) (x i) (y i).

Definition q193878_relation_ring_isomorphism
    (source target : Type)
    (source_equal : source -> source -> Prop)
    (target_equal : target -> target -> Prop)
    (source_zero : source)
    (target_zero : target)
    (source_one : source)
    (target_one : target)
    (source_add : source -> source -> source)
    (target_add : target -> target -> target)
    (source_mul : source -> source -> source)
    (target_mul : target -> target -> target)
    (source_neg : source -> source)
    (target_neg : target -> target)
    (forward : source -> target) : Prop :=
  (forall x y : source,
      source_equal x y ->
      target_equal (forward x) (forward y)) /\
  target_equal (forward source_zero) target_zero /\
  target_equal (forward source_one) target_one /\
  (forall x y : source,
      target_equal
        (forward (source_add x y))
        (target_add (forward x) (forward y))) /\
  (forall x y : source,
      target_equal
        (forward (source_mul x y))
        (target_mul (forward x) (forward y))) /\
  (forall x : source,
      target_equal (forward (source_neg x)) (target_neg (forward x))) /\
  exists backward : target -> source,
    (forall x y : target,
        target_equal x y ->
        source_equal (backward x) (backward y)) /\
    (forall x : source,
        source_equal (backward (forward x)) x) /\
    forall y : target,
      target_equal (forward (backward y)) y.

Definition q193878_product_zero
    {R index : Type}
    (CR : q193878_commutative_ring R) : index -> R :=
  fun _ => q193878_zero CR.

Definition q193878_product_one
    {R index : Type}
    (CR : q193878_commutative_ring R) : index -> R :=
  fun _ => q193878_one CR.

Definition q193878_product_add
    {R index : Type}
    (CR : q193878_commutative_ring R)
    (x y : index -> R) : index -> R :=
  fun i => q193878_add CR (x i) (y i).

Definition q193878_product_mul
    {R index : Type}
    (CR : q193878_commutative_ring R)
    (x y : index -> R) : index -> R :=
  fun i => q193878_mul CR (x i) (y i).

Definition q193878_product_neg
    {R index : Type}
    (CR : q193878_commutative_ring R)
    (x : index -> R) : index -> R :=
  fun i => q193878_neg CR (x i).

Definition q193878_diagonal
    {R index : Type} (x : R) : index -> R :=
  fun _ => x.

Definition q193878_canonical_quotient_ring_isomorphism
    {R index : Type}
    (CR : q193878_commutative_ring R)
    (ideals : index -> @q193878_ideal R CR) : Prop :=
  @q193878_relation_ring_isomorphism
    R (index -> R)
    (q193878_intersection_quotient_equal ideals)
    (q193878_product_quotient_equal ideals)
    (q193878_zero CR)
    (q193878_product_zero CR)
    (q193878_one CR)
    (q193878_product_one CR)
    (q193878_add CR)
    (q193878_product_add CR)
    (q193878_mul CR)
    (q193878_product_mul CR)
    (q193878_neg CR)
    (q193878_product_neg CR)
    q193878_diagonal.

Theorem Ideal_quotientInfRingEquivPiQuotient :
  forall (R : Type)
         (CR : q193878_commutative_ring R)
         (index : Type)
         (ideals : index -> @q193878_ideal R CR),
    q193878_is_finite index ->
    q193878_pairwise_comaximal ideals ->
    @q193878_canonical_quotient_ring_isomorphism R index CR ideals.
Admitted.
