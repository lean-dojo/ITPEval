(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7525341
  (thousand-theorems__rocq__Q7525341), "Sion's minimax theorem": for
  quasiconvex lower-semicontinuous slices and quasiconcave
  upper-semicontinuous slices on convex subsets of real topological vector
  spaces and values in a densely ordered linear order, with the first set
  nonempty and compact, the four explicit IsLUB/IsGLB hypotheses of the
  canonical statement imply the minimax equality. This file contains no proof.
*)

From Stdlib Require Import Reals List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q7525341_set (A : Type) : Type := A -> Prop.

Definition q7525341_subset {A : Type}
    (S T : q7525341_set A) : Prop :=
  forall x : A, S x -> T x.

Record q7525341_linear_order (B : Type) : Type := {
  q7525341_le : B -> B -> Prop;
  q7525341_le_refl :
    forall x : B, q7525341_le x x;
  q7525341_le_antisym :
    forall x y : B,
      q7525341_le x y ->
      q7525341_le y x ->
      x = y;
  q7525341_le_trans :
    forall x y z : B,
      q7525341_le x y ->
      q7525341_le y z ->
      q7525341_le x z;
  q7525341_le_total :
    forall x y : B,
      q7525341_le x y \/ q7525341_le y x
}.

Arguments q7525341_le {B} _ _ _.

Definition q7525341_lt {B : Type}
    (O : q7525341_linear_order B)
    (x y : B) : Prop :=
  q7525341_le O x y /\ x <> y.

Definition q7525341_densely_ordered
    {B : Type}
    (O : q7525341_linear_order B) : Prop :=
  forall x y : B,
    q7525341_lt O x y ->
    exists z : B,
      q7525341_lt O x z /\
      q7525341_lt O z y.

Record q7525341_topological_space (A : Type) : Type := {
  q7525341_is_open : q7525341_set A -> Prop;
  q7525341_open_extensional :
    forall U V : q7525341_set A,
      (forall x : A, U x <-> V x) ->
      (q7525341_is_open U <-> q7525341_is_open V);
  q7525341_open_univ :
    q7525341_is_open (fun _ : A => True);
  q7525341_open_intersection :
    forall U V : q7525341_set A,
      q7525341_is_open U ->
      q7525341_is_open V ->
      q7525341_is_open (fun x : A => U x /\ V x);
  q7525341_open_union :
    forall family : q7525341_set (q7525341_set A),
      (forall U : q7525341_set A,
        family U -> q7525341_is_open U) ->
      q7525341_is_open
        (fun x : A =>
          exists U : q7525341_set A, family U /\ U x)
}.

Arguments q7525341_is_open {A} _ _.

Record q7525341_real_module (E : Type) : Type := {
  q7525341_zero : E;
  q7525341_add : E -> E -> E;
  q7525341_neg : E -> E;
  q7525341_smul : R -> E -> E;
  q7525341_add_assoc :
    forall x y z : E,
      q7525341_add x (q7525341_add y z) =
      q7525341_add (q7525341_add x y) z;
  q7525341_add_comm :
    forall x y : E,
      q7525341_add x y = q7525341_add y x;
  q7525341_add_zero :
    forall x : E,
      q7525341_add x q7525341_zero = x;
  q7525341_add_neg :
    forall x : E,
      q7525341_add x (q7525341_neg x) = q7525341_zero;
  q7525341_one_smul :
    forall x : E,
      q7525341_smul 1 x = x;
  q7525341_mul_smul :
    forall (a b : R) (x : E),
      q7525341_smul (a * b) x =
      q7525341_smul a (q7525341_smul b x);
  q7525341_add_smul :
    forall (a b : R) (x : E),
      q7525341_smul (a + b) x =
      q7525341_add
        (q7525341_smul a x)
        (q7525341_smul b x);
  q7525341_smul_add :
    forall (a : R) (x y : E),
      q7525341_smul a (q7525341_add x y) =
      q7525341_add
        (q7525341_smul a x)
        (q7525341_smul a y)
}.

Arguments q7525341_zero {E} _.
Arguments q7525341_add {E} _ _ _.
Arguments q7525341_neg {E} _ _.
Arguments q7525341_smul {E} _ _ _.

Definition q7525341_real_open
    (U : q7525341_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q7525341_product_open
    {A B : Type}
    (TA : q7525341_topological_space A)
    (TB : q7525341_topological_space B)
    (U : q7525341_set (A * B)) : Prop :=
  forall (a : A) (b : B),
    U (a, b) ->
    exists V : q7525341_set A,
    exists W : q7525341_set B,
      q7525341_is_open TA V /\
      q7525341_is_open TB W /\
      V a /\
      W b /\
      forall (a' : A) (b' : B),
        V a' ->
        W b' ->
        U (a', b').

Definition q7525341_real_product_open
    {E : Type}
    (T : q7525341_topological_space E)
    (U : q7525341_set (R * E)) : Prop :=
  forall (a : R) (x : E),
    U (a, x) ->
    exists A : q7525341_set R,
    exists V : q7525341_set E,
      q7525341_real_open A /\
      q7525341_is_open T V /\
      A a /\
      V x /\
      forall (b : R) (y : E),
        A b ->
        V y ->
        U (b, y).

Definition q7525341_continuous_add
    {E : Type}
    (V : q7525341_real_module E)
    (T : q7525341_topological_space E) : Prop :=
  forall U : q7525341_set E,
    q7525341_is_open T U ->
    q7525341_product_open T T
      (fun p : E * E =>
        U (q7525341_add V (fst p) (snd p))).

Definition q7525341_continuous_neg
    {E : Type}
    (V : q7525341_real_module E)
    (T : q7525341_topological_space E) : Prop :=
  forall U : q7525341_set E,
    q7525341_is_open T U ->
    q7525341_is_open T
      (fun x : E => U (q7525341_neg V x)).

Definition q7525341_continuous_smul
    {E : Type}
    (V : q7525341_real_module E)
    (T : q7525341_topological_space E) : Prop :=
  forall U : q7525341_set E,
    q7525341_is_open T U ->
    q7525341_real_product_open T
      (fun p : R * E =>
        U (q7525341_smul V (fst p) (snd p))).

Definition q7525341_is_real_topological_vector_space
    {E : Type}
    (V : q7525341_real_module E)
    (T : q7525341_topological_space E) : Prop :=
  q7525341_continuous_add V T /\
  q7525341_continuous_neg V T /\
  q7525341_continuous_smul V T.

Definition q7525341_convex
    {E : Type}
    (V : q7525341_real_module E)
    (S : q7525341_set E) : Prop :=
  forall (x y : E) (a b : R),
    S x ->
    S y ->
    0 <= a ->
    0 <= b ->
    a + b = 1 ->
    S
      (q7525341_add V
        (q7525341_smul V a x)
        (q7525341_smul V b y)).

Definition q7525341_is_compact
    {E : Type}
    (T : q7525341_topological_space E)
    (K : q7525341_set E) : Prop :=
  forall cover : q7525341_set (q7525341_set E),
    (forall U : q7525341_set E,
      cover U -> q7525341_is_open T U) ->
    (forall x : E,
      K x ->
      exists U : q7525341_set E,
        cover U /\ U x) ->
    exists finite_cover : list (q7525341_set E),
      Forall cover finite_cover /\
      forall x : E,
        K x ->
        exists U : q7525341_set E,
          In U finite_cover /\ U x.

Definition q7525341_lower_semicontinuous_on
    {E B : Type}
    (T : q7525341_topological_space E)
    (O : q7525341_linear_order B)
    (g : E -> B)
    (S : q7525341_set E) : Prop :=
  forall x : E,
    S x ->
    forall b : B,
      q7525341_lt O b (g x) ->
      exists U : q7525341_set E,
        q7525341_is_open T U /\
        U x /\
        forall z : E,
          U z ->
          S z ->
          q7525341_lt O b (g z).

Definition q7525341_upper_semicontinuous_on
    {E B : Type}
    (T : q7525341_topological_space E)
    (O : q7525341_linear_order B)
    (g : E -> B)
    (S : q7525341_set E) : Prop :=
  forall x : E,
    S x ->
    forall b : B,
      q7525341_lt O (g x) b ->
      exists U : q7525341_set E,
        q7525341_is_open T U /\
        U x /\
        forall z : E,
          U z ->
          S z ->
          q7525341_lt O (g z) b.

Definition q7525341_quasiconvex_on
    {E B : Type}
    (V : q7525341_real_module E)
    (O : q7525341_linear_order B)
    (S : q7525341_set E)
    (g : E -> B) : Prop :=
  forall b : B,
    q7525341_convex V
      (fun x : E => S x /\ q7525341_le O (g x) b).

Definition q7525341_quasiconcave_on
    {E B : Type}
    (V : q7525341_real_module E)
    (O : q7525341_linear_order B)
    (S : q7525341_set E)
    (g : E -> B) : Prop :=
  forall b : B,
    q7525341_convex V
      (fun x : E => S x /\ q7525341_le O b (g x)).

Definition q7525341_is_upper_bound
    {B : Type}
    (O : q7525341_linear_order B)
    (S : q7525341_set B)
    (bound : B) : Prop :=
  forall z : B,
    S z ->
    q7525341_le O z bound.

Definition q7525341_is_lower_bound
    {B : Type}
    (O : q7525341_linear_order B)
    (S : q7525341_set B)
    (bound : B) : Prop :=
  forall z : B,
    S z ->
    q7525341_le O bound z.

Definition q7525341_is_lub
    {B : Type}
    (O : q7525341_linear_order B)
    (S : q7525341_set B)
    (least_upper_bound : B) : Prop :=
  q7525341_is_upper_bound O S least_upper_bound /\
  forall bound : B,
    q7525341_is_upper_bound O S bound ->
    q7525341_le O least_upper_bound bound.

Definition q7525341_is_glb
    {B : Type}
    (O : q7525341_linear_order B)
    (S : q7525341_set B)
    (greatest_lower_bound : B) : Prop :=
  q7525341_is_lower_bound O S greatest_lower_bound /\
  forall bound : B,
    q7525341_is_lower_bound O S bound ->
    q7525341_le O bound greatest_lower_bound.

(* The final value-and-bound binders below are the four explicit IsLUB/IsGLB
   arguments of the canonical Sion.minimax statement. *)
Theorem sion_minimax
    (E F B : Type)
    (VE : q7525341_real_module E)
    (VF : q7525341_real_module F)
    (TE : q7525341_topological_space E)
    (TF : q7525341_topological_space F)
    (O : q7525341_linear_order B)
    (X : q7525341_set E)
    (Y : q7525341_set F)
    (f : E -> F -> B)
    (dense_B : q7525341_densely_ordered O)
    (topological_vector_E :
      q7525341_is_real_topological_vector_space VE TE)
    (topological_vector_F :
      q7525341_is_real_topological_vector_space VF TF)
    (nonempty_X : exists x : E, X x)
    (convex_X : q7525341_convex VE X)
    (compact_X : q7525341_is_compact TE X)
    (lower_semicontinuous_slices :
      forall y : F,
      Y y ->
      q7525341_lower_semicontinuous_on
        TE O (fun x : E => f x y) X)
    (quasiconvex_slices :
      forall y : F,
      Y y ->
      q7525341_quasiconvex_on
        VE O X (fun x : E => f x y))
    (convex_Y : q7525341_convex VF Y)
    (upper_semicontinuous_slices :
      forall x : E,
      X x ->
      q7525341_upper_semicontinuous_on
        TF O (fun y : F => f x y) Y)
    (quasiconcave_slices :
      forall x : E,
      X x ->
      q7525341_quasiconcave_on
        VF O Y (fun y : F => f x y))
    (sup_y : E -> B)
    (hsup_y :
      forall x : E,
      X x ->
      q7525341_is_lub O
        (fun z : B =>
          exists y : F, Y y /\ z = f x y)
        (sup_y x))
    (inf_sup : B)
    (hinf_sup :
      q7525341_is_glb O
        (fun z : B =>
          exists x : E, X x /\ z = sup_y x)
        inf_sup)
    (inf_x : F -> B)
    (hinf_x :
      forall y : F,
      Y y ->
      q7525341_is_glb O
        (fun z : B =>
          exists x : E, X x /\ z = f x y)
        (inf_x y))
    (sup_inf : B)
    (hsup_inf :
      q7525341_is_lub O
        (fun z : B =>
          exists y : F, Y y /\ z = inf_x y)
        sup_inf) :
  inf_sup = sup_inf.
Admitted.
