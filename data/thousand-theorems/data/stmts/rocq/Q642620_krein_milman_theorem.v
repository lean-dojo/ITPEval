(*
  Statement-only formalization of Thousand Theorems corpus artifact Q642620
  (thousand-theorems__rocq__Q642620), "Krein–Milman theorem": every compact
  convex subset of a real locally convex Hausdorff topological vector space
  is the closure of the convex hull of its extreme points. This file contains
  no proof.
*)

From Stdlib Require Import Reals List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q642620_set (A : Type) : Type := A -> Prop.

Definition q642620_subset {A : Type}
    (S T : q642620_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q642620_same_set {A : Type}
    (S T : q642620_set A) : Prop :=
  forall x : A, S x <-> T x.

Record q642620_real_module (E : Type) : Type := {
  q642620_zero : E;
  q642620_add : E -> E -> E;
  q642620_neg : E -> E;
  q642620_smul : R -> E -> E;
  q642620_add_assoc :
    forall x y z : E,
      q642620_add x (q642620_add y z) =
      q642620_add (q642620_add x y) z;
  q642620_add_comm :
    forall x y : E,
      q642620_add x y = q642620_add y x;
  q642620_add_zero :
    forall x : E,
      q642620_add x q642620_zero = x;
  q642620_add_neg :
    forall x : E,
      q642620_add x (q642620_neg x) = q642620_zero;
  q642620_one_smul :
    forall x : E,
      q642620_smul 1 x = x;
  q642620_mul_smul :
    forall (a b : R) (x : E),
      q642620_smul (a * b) x =
      q642620_smul a (q642620_smul b x);
  q642620_add_smul :
    forall (a b : R) (x : E),
      q642620_smul (a + b) x =
      q642620_add (q642620_smul a x) (q642620_smul b x);
  q642620_smul_add :
    forall (a : R) (x y : E),
      q642620_smul a (q642620_add x y) =
      q642620_add (q642620_smul a x) (q642620_smul a y)
}.

Arguments q642620_zero {E} _.
Arguments q642620_add {E} _ _ _.
Arguments q642620_neg {E} _ _.
Arguments q642620_smul {E} _ _ _.

Definition q642620_convex
    {E : Type}
    (V : q642620_real_module E)
    (S : q642620_set E) : Prop :=
  forall (x y : E) (t : R),
    S x ->
    S y ->
    0 <= t ->
    t <= 1 ->
    S
      (q642620_add V
        (q642620_smul V t x)
        (q642620_smul V (1 - t) y)).

Definition q642620_convex_hull
    {E : Type}
    (V : q642620_real_module E)
    (S : q642620_set E) : q642620_set E :=
  fun x : E =>
    forall C : q642620_set E,
      q642620_convex V C ->
      q642620_subset S C ->
      C x.

Record q642620_topological_space (E : Type) : Type := {
  q642620_is_open : q642620_set E -> Prop;
  q642620_open_ext :
    forall U W : q642620_set E,
      (forall x : E, U x <-> W x) ->
      (q642620_is_open U <-> q642620_is_open W);
  q642620_open_univ :
    q642620_is_open (fun _ : E => True);
  q642620_open_inter :
    forall U W : q642620_set E,
      q642620_is_open U ->
      q642620_is_open W ->
      q642620_is_open (fun x : E => U x /\ W x);
  q642620_open_sUnion :
    forall family : q642620_set (q642620_set E),
      (forall U : q642620_set E,
        family U -> q642620_is_open U) ->
      q642620_is_open
        (fun x : E =>
          exists U : q642620_set E, family U /\ U x)
}.

Arguments q642620_is_open {E} _ _.

Definition q642620_is_closed
    {E : Type}
    (T : q642620_topological_space E)
    (C : q642620_set E) : Prop :=
  q642620_is_open T (fun x : E => ~ C x).

Definition q642620_closure
    {E : Type}
    (T : q642620_topological_space E)
    (S : q642620_set E) : q642620_set E :=
  fun x : E =>
    forall C : q642620_set E,
      q642620_is_closed T C ->
      q642620_subset S C ->
      C x.

Definition q642620_real_open (U : q642620_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R, Rabs (y - x) < epsilon -> U y.

Definition q642620_hausdorff
    {E : Type}
    (T : q642620_topological_space E) : Prop :=
  forall x y : E,
    x <> y ->
    exists U W : q642620_set E,
      q642620_is_open T U /\
      q642620_is_open T W /\
      U x /\
      W y /\
      forall z : E, ~ (U z /\ W z).

Definition q642620_add_continuous
    {E : Type}
    (V : q642620_real_module E)
    (T : q642620_topological_space E) : Prop :=
  forall (x y : E) (U : q642620_set E),
    q642620_is_open T U ->
    U (q642620_add V x y) ->
    exists W Z : q642620_set E,
      q642620_is_open T W /\
      q642620_is_open T Z /\
      W x /\
      Z y /\
      forall x' y' : E,
        W x' ->
        Z y' ->
        U (q642620_add V x' y').

Definition q642620_neg_continuous
    {E : Type}
    (V : q642620_real_module E)
    (T : q642620_topological_space E) : Prop :=
  forall (x : E) (U : q642620_set E),
    q642620_is_open T U ->
    U (q642620_neg V x) ->
    exists W : q642620_set E,
      q642620_is_open T W /\
      W x /\
      forall y : E, W y -> U (q642620_neg V y).

Definition q642620_smul_continuous
    {E : Type}
    (V : q642620_real_module E)
    (T : q642620_topological_space E) : Prop :=
  forall (a : R) (x : E) (U : q642620_set E),
    q642620_is_open T U ->
    U (q642620_smul V a x) ->
    exists A : q642620_set R,
    exists W : q642620_set E,
      q642620_real_open A /\
      q642620_is_open T W /\
      A a /\
      W x /\
      forall (b : R) (y : E),
        A b ->
        W y ->
        U (q642620_smul V b y).

Record q642620_locally_convex_hausdorff_tvs
    {E : Type}
    (V : q642620_real_module E)
    (T : q642620_topological_space E) : Prop := {
  q642620_tvs_hausdorff :
    q642620_hausdorff T;
  q642620_tvs_add_continuous :
    q642620_add_continuous V T;
  q642620_tvs_neg_continuous :
    q642620_neg_continuous V T;
  q642620_tvs_smul_continuous :
    q642620_smul_continuous V T;
  q642620_tvs_locally_convex :
    forall U : q642620_set E,
      q642620_is_open T U ->
      U (q642620_zero V) ->
      exists W : q642620_set E,
        q642620_is_open T W /\
        q642620_convex V W /\
        W (q642620_zero V) /\
        q642620_subset W U
}.

Definition q642620_is_compact
    {E : Type}
    (T : q642620_topological_space E)
    (K : q642620_set E) : Prop :=
  forall cover : q642620_set (q642620_set E),
    (forall U : q642620_set E,
      cover U -> q642620_is_open T U) ->
    (forall x : E,
      K x ->
      exists U : q642620_set E, cover U /\ U x) ->
    exists finite_cover : list (q642620_set E),
      Forall cover finite_cover /\
      forall x : E,
        K x ->
        exists U : q642620_set E,
          In U finite_cover /\ U x.

Definition q642620_extreme_points
    {E : Type}
    (V : q642620_real_module E)
    (S : q642620_set E) : q642620_set E :=
  fun x : E =>
    S x /\
    forall (y z : E) (t : R),
      S y ->
      S z ->
      0 < t ->
      t < 1 ->
      x =
        q642620_add V
          (q642620_smul V t y)
          (q642620_smul V (1 - t) z) ->
      y = x /\ z = x.

Theorem closure_convexHull_extremePoints :
  forall (E : Type)
         (V : q642620_real_module E)
         (T : q642620_topological_space E),
    q642620_locally_convex_hausdorff_tvs V T ->
    forall S : q642620_set E,
      q642620_is_compact T S ->
      q642620_convex V S ->
      q642620_same_set
        (q642620_closure T
          (q642620_convex_hull V
            (q642620_extreme_points V S)))
        S.
Admitted.
