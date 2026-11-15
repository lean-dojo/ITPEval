(*
  Statement-only formalization of Thousand Theorems corpus artifact Q609612
  (thousand-theorems__rocq__Q609612), "Knaster–Tarski theorem": the fixed
  points of a monotone self-map of a complete lattice themselves form a
  complete lattice under the inherited order. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Record q609612_complete_lattice (A : Type) : Type := {
  q609612_le : A -> A -> Prop;
  q609612_le_refl :
    forall x : A, q609612_le x x;
  q609612_le_trans :
    forall x y z : A,
      q609612_le x y ->
      q609612_le y z ->
      q609612_le x z;
  q609612_le_antisym :
    forall x y : A,
      q609612_le x y ->
      q609612_le y x ->
      x = y;
  q609612_supremum : (A -> Prop) -> A;
  q609612_le_supremum :
    forall (S : A -> Prop) (x : A),
      S x ->
      q609612_le x (q609612_supremum S);
  q609612_supremum_le :
    forall (S : A -> Prop) (upper : A),
      (forall x : A, S x -> q609612_le x upper) ->
      q609612_le (q609612_supremum S) upper;
  q609612_infimum : (A -> Prop) -> A;
  q609612_infimum_le :
    forall (S : A -> Prop) (x : A),
      S x ->
      q609612_le (q609612_infimum S) x;
  q609612_le_infimum :
    forall (S : A -> Prop) (lower : A),
      (forall x : A, S x -> q609612_le lower x) ->
      q609612_le lower (q609612_infimum S)
}.

Arguments q609612_le {A} _ _ _.

Record q609612_order_hom
    (A : Type) (L : q609612_complete_lattice A) : Type := {
  q609612_hom_fun : A -> A;
  q609612_hom_monotone :
    forall x y : A,
      q609612_le L x y ->
      q609612_le L (q609612_hom_fun x) (q609612_hom_fun y)
}.

Arguments q609612_order_hom A L : clear implicits.
Arguments q609612_hom_fun {A L} _ _.

Definition q609612_fixed_points
    {A : Type}
    {L : q609612_complete_lattice A}
    (f : q609612_order_hom A L) : A -> Prop :=
  fun x : A => q609612_hom_fun f x = x.

Record q609612_fixed_point
    {A : Type}
    {L : q609612_complete_lattice A}
    (f : q609612_order_hom A L) : Type := {
  q609612_fixed_point_val : A;
  q609612_fixed_point_property :
    q609612_hom_fun f q609612_fixed_point_val =
    q609612_fixed_point_val
}.

Arguments q609612_fixed_point {A L} f.
Arguments q609612_fixed_point_val {A L f} _.

Definition q609612_fixed_point_equiv
    {A : Type}
    {L : q609612_complete_lattice A}
    (f : q609612_order_hom A L)
    (x y : q609612_fixed_point f) : Prop :=
  q609612_fixed_point_val x = q609612_fixed_point_val y.

Arguments q609612_fixed_point_equiv {A L} f _ _.

Definition q609612_fixed_point_le
    {A : Type}
    {L : q609612_complete_lattice A}
    (f : q609612_order_hom A L)
    (x y : q609612_fixed_point f) : Prop :=
  q609612_le L
    (q609612_fixed_point_val x)
    (q609612_fixed_point_val y).

Arguments q609612_fixed_point_le {A L} f _ _.

Record q609612_setoid_subset
    (A : Type)
    (equiv : A -> A -> Prop) : Type := {
  q609612_setoid_subset_carrier : A -> Prop;
  q609612_setoid_subset_compatible :
    forall x y : A,
      equiv x y ->
      (q609612_setoid_subset_carrier x <->
       q609612_setoid_subset_carrier y)
}.

Arguments q609612_setoid_subset A equiv : clear implicits.
Arguments q609612_setoid_subset_carrier {A equiv} _ _.

Record q609612_complete_lattice_structure
    (A : Type)
    (equiv : A -> A -> Prop)
    (le : A -> A -> Prop) : Type := {
  q609612_structure_equiv_refl :
    forall x : A, equiv x x;
  q609612_structure_equiv_sym :
    forall x y : A,
      equiv x y ->
      equiv y x;
  q609612_structure_equiv_trans :
    forall x y z : A,
      equiv x y ->
      equiv y z ->
      equiv x z;
  q609612_structure_le_compatible :
    forall x x' y y' : A,
      equiv x x' ->
      equiv y y' ->
      (le x y <-> le x' y');
  q609612_structure_le_refl :
    forall x : A, le x x;
  q609612_structure_le_trans :
    forall x y z : A,
      le x y ->
      le y z ->
      le x z;
  q609612_structure_le_antisym :
    forall x y : A,
      le x y ->
      le y x ->
      equiv x y;
  q609612_structure_bottom : A;
  q609612_structure_bottom_le :
    forall x : A, le q609612_structure_bottom x;
  q609612_structure_top : A;
  q609612_structure_le_top :
    forall x : A, le x q609612_structure_top;
  q609612_structure_sup : A -> A -> A;
  q609612_structure_sup_compatible :
    forall x x' y y' : A,
      equiv x x' ->
      equiv y y' ->
      equiv
        (q609612_structure_sup x y)
        (q609612_structure_sup x' y');
  q609612_structure_le_sup_left :
    forall x y : A, le x (q609612_structure_sup x y);
  q609612_structure_le_sup_right :
    forall x y : A, le y (q609612_structure_sup x y);
  q609612_structure_sup_le :
    forall x y upper : A,
      le x upper ->
      le y upper ->
      le (q609612_structure_sup x y) upper;
  q609612_structure_inf : A -> A -> A;
  q609612_structure_inf_compatible :
    forall x x' y y' : A,
      equiv x x' ->
      equiv y y' ->
      equiv
        (q609612_structure_inf x y)
        (q609612_structure_inf x' y');
  q609612_structure_inf_le_left :
    forall x y : A, le (q609612_structure_inf x y) x;
  q609612_structure_inf_le_right :
    forall x y : A, le (q609612_structure_inf x y) y;
  q609612_structure_le_inf :
    forall lower x y : A,
      le lower x ->
      le lower y ->
      le lower (q609612_structure_inf x y);
  q609612_structure_supremum :
    q609612_setoid_subset A equiv -> A;
  q609612_structure_supremum_compatible :
    forall S T : q609612_setoid_subset A equiv,
      (forall x : A,
        q609612_setoid_subset_carrier S x <->
        q609612_setoid_subset_carrier T x) ->
      equiv
        (q609612_structure_supremum S)
        (q609612_structure_supremum T);
  q609612_structure_le_supremum :
    forall (S : q609612_setoid_subset A equiv) (x : A),
      q609612_setoid_subset_carrier S x ->
      le x (q609612_structure_supremum S);
  q609612_structure_supremum_le :
    forall (S : q609612_setoid_subset A equiv) (upper : A),
      (forall x : A,
        q609612_setoid_subset_carrier S x ->
        le x upper) ->
      le (q609612_structure_supremum S) upper;
  q609612_structure_infimum :
    q609612_setoid_subset A equiv -> A;
  q609612_structure_infimum_compatible :
    forall S T : q609612_setoid_subset A equiv,
      (forall x : A,
        q609612_setoid_subset_carrier S x <->
        q609612_setoid_subset_carrier T x) ->
      equiv
        (q609612_structure_infimum S)
        (q609612_structure_infimum T);
  q609612_structure_infimum_le :
    forall (S : q609612_setoid_subset A equiv) (x : A),
      q609612_setoid_subset_carrier S x ->
      le (q609612_structure_infimum S) x;
  q609612_structure_le_infimum :
    forall (S : q609612_setoid_subset A equiv) (lower : A),
      (forall x : A,
        q609612_setoid_subset_carrier S x ->
        le lower x) ->
      le lower (q609612_structure_infimum S)
}.

Module fixedPoints.

Theorem completeLattice :
  forall (A : Type)
         (L : q609612_complete_lattice A)
         (f : q609612_order_hom A L),
    @q609612_complete_lattice_structure
      (q609612_fixed_point f)
      (q609612_fixed_point_equiv f)
      (q609612_fixed_point_le f).
Admitted.

End fixedPoints.
