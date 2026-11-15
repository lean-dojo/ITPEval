(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5638886
  (thousand-theorems__rocq__Q5638886), "Hahn embedding theorem": every
  linearly ordered abelian group embeds injectively by an order-preserving
  additive homomorphism into the real Hahn series indexed by its finite
  Archimedean classes, with leading class equal to the class of the source
  element. This file contains no proof.
*)

From Stdlib Require Import Reals Arith Wellfounded.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q5638886_ordered_add_comm_group (M : Type) : Type := {
  q5638886_zero : M;
  q5638886_add : M -> M -> M;
  q5638886_neg : M -> M;
  q5638886_le : M -> M -> Prop;
  q5638886_add_assoc :
    forall x y z : M,
      q5638886_add x (q5638886_add y z) =
      q5638886_add (q5638886_add x y) z;
  q5638886_add_comm :
    forall x y : M,
      q5638886_add x y = q5638886_add y x;
  q5638886_add_zero :
    forall x : M,
      q5638886_add x q5638886_zero = x;
  q5638886_add_neg :
    forall x : M,
      q5638886_add x (q5638886_neg x) = q5638886_zero;
  q5638886_le_refl :
    forall x : M, q5638886_le x x;
  q5638886_le_trans :
    forall x y z : M,
      q5638886_le x y ->
      q5638886_le y z ->
      q5638886_le x z;
  q5638886_le_antisym :
    forall x y : M,
      q5638886_le x y ->
      q5638886_le y x ->
      x = y;
  q5638886_le_total :
    forall x y : M,
      q5638886_le x y \/ q5638886_le y x;
  q5638886_add_le_add_left :
    forall x y z : M,
      q5638886_le x y ->
      q5638886_le
        (q5638886_add z x) (q5638886_add z y)
}.

Arguments q5638886_zero {M} _.
Arguments q5638886_add {M} _ _ _.
Arguments q5638886_neg {M} _ _.
Arguments q5638886_le {M} _ _ _.

Fixpoint q5638886_nsmul
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (n : nat) (x : M) : M :=
  match n with
  | O => q5638886_zero grp
  | S k => q5638886_add grp x (q5638886_nsmul grp k x)
  end.

Definition q5638886_is_abs
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (x a : M) : Prop :=
  (q5638886_le grp (q5638886_zero grp) x /\ a = x) \/
  (q5638886_le grp x (q5638886_zero grp) /\
   a = q5638886_neg grp x).

(* The order on Archimedean classes reverses domination, as in mathlib:
   [x] <= [y] exactly when |y| <= n |x| for some natural number n. *)
Definition q5638886_arch_preorder
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (x y : M) : Prop :=
  exists (n : nat) (ax ay : M),
    q5638886_is_abs grp x ax /\
    q5638886_is_abs grp y ay /\
    q5638886_le grp ay (q5638886_nsmul grp n ax).

Definition q5638886_arch_equiv
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (x y : M) : Prop :=
  q5638886_arch_preorder grp x y /\
  q5638886_arch_preorder grp y x.

(* A setoid presentation of the quotient of nonzero elements by
   Archimedean equivalence. *)
Record q5638886_finite_arch_class
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M) : Type := {
  q5638886_class_repr : M;
  q5638886_class_repr_nonzero :
    q5638886_class_repr <> q5638886_zero grp
}.

Arguments q5638886_class_repr {M grp} _.

Definition q5638886_class_equiv
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (c d : q5638886_finite_arch_class grp) : Prop :=
  q5638886_arch_equiv grp
    (q5638886_class_repr c) (q5638886_class_repr d).

Definition q5638886_class_le
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (c d : q5638886_finite_arch_class grp) : Prop :=
  q5638886_arch_preorder grp
    (q5638886_class_repr c) (q5638886_class_repr d).

Definition q5638886_class_lt
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (c d : q5638886_finite_arch_class grp) : Prop :=
  q5638886_class_le c d /\ ~ q5638886_class_le d c.

(* Real Hahn series on the quotient setoid. The coefficient function is
   invariant under class equivalence, and its support is well-founded. *)
Record q5638886_hahn_series
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M) : Type := {
  q5638886_coeff :
    q5638886_finite_arch_class grp -> R;
  q5638886_coeff_respects :
    forall c d : q5638886_finite_arch_class grp,
      q5638886_class_equiv c d ->
      q5638886_coeff c = q5638886_coeff d;
  q5638886_support_well_founded :
    well_founded
      (fun c d : q5638886_finite_arch_class grp =>
        q5638886_coeff c <> 0 /\
        q5638886_coeff d <> 0 /\
        q5638886_class_lt c d)
}.

Arguments q5638886_coeff {M grp} _ _.

Definition q5638886_hahn_support
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s : q5638886_hahn_series grp)
    (c : q5638886_finite_arch_class grp) : Prop :=
  q5638886_coeff s c <> 0.

Definition q5638886_hahn_equal
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s t : q5638886_hahn_series grp) : Prop :=
  forall c : q5638886_finite_arch_class grp,
    q5638886_coeff s c = q5638886_coeff t c.

Definition q5638886_hahn_zero
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s : q5638886_hahn_series grp) : Prop :=
  forall c : q5638886_finite_arch_class grp,
    q5638886_coeff s c = 0.

Definition q5638886_hahn_lt
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s t : q5638886_hahn_series grp) : Prop :=
  exists i : q5638886_finite_arch_class grp,
    (forall j : q5638886_finite_arch_class grp,
      q5638886_class_lt j i ->
      q5638886_coeff s j = q5638886_coeff t j) /\
    q5638886_coeff s i < q5638886_coeff t i.

Definition q5638886_hahn_le
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s t : q5638886_hahn_series grp) : Prop :=
  q5638886_hahn_equal s t \/ q5638886_hahn_lt s t.

Definition q5638886_ordered_add_monoid_hom
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (f : M -> q5638886_hahn_series grp) : Prop :=
  (forall c : q5638886_finite_arch_class grp,
    q5638886_coeff (f (q5638886_zero grp)) c = 0) /\
  (forall (x y : M) (c : q5638886_finite_arch_class grp),
    q5638886_coeff (f (q5638886_add grp x y)) c =
    q5638886_coeff (f x) c + q5638886_coeff (f y) c) /\
  forall x y : M,
    q5638886_le grp x y ->
    q5638886_hahn_le (f x) (f y).

Definition q5638886_injective
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (f : M -> q5638886_hahn_series grp) : Prop :=
  forall x y : M,
    q5638886_hahn_equal (f x) (f y) ->
    x = y.

Definition q5638886_minimal_support_class
    {M : Type}
    {grp : q5638886_ordered_add_comm_group M}
    (s : q5638886_hahn_series grp)
    (c : q5638886_finite_arch_class grp) : Prop :=
  q5638886_hahn_support s c /\
  forall d : q5638886_finite_arch_class grp,
    q5638886_hahn_support s d ->
    q5638886_class_le c d.

(* This is the setoid expansion of
   mk(a) = withTopOrderIso(orderTop(s)): zero support represents top, while
   nonzero support is represented by its least finite Archimedean class. *)
Definition q5638886_leading_class_matches
    {M : Type}
    (grp : q5638886_ordered_add_comm_group M)
    (a : M)
    (s : q5638886_hahn_series grp) : Prop :=
  (q5638886_hahn_zero s /\
   q5638886_arch_equiv grp a (q5638886_zero grp)) \/
  exists c : q5638886_finite_arch_class grp,
    q5638886_minimal_support_class s c /\
    q5638886_arch_equiv grp a (q5638886_class_repr c).

Theorem hahnEmbedding_isOrderedAddMonoid :
  forall (M : Type)
         (grp : q5638886_ordered_add_comm_group M),
    exists f : M -> q5638886_hahn_series grp,
      @q5638886_ordered_add_monoid_hom M grp f /\
      @q5638886_injective M grp f /\
      forall a : M,
        @q5638886_leading_class_matches M grp a (f a).
Admitted.
