(*
  Statement-only formalization of Thousand Theorems corpus artifact Q537618
  (thousand-theorems__rocq__Q537618), "Banach–Alaoglu theorem": the polar of
  a neighborhood of zero in a seminormed space over a proper nontrivially
  normed field is compact in the weak-star topology. This file contains no
  proof.
*)

From Stdlib Require Import List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q537618_set (A : Type) : Type := A -> Prop.

Record q537618_normed_field (K : Type) : Type := {
  q537618_fzero : K;
  q537618_fone : K;
  q537618_fadd : K -> K -> K;
  q537618_fmul : K -> K -> K;
  q537618_fneg : K -> K;
  q537618_finv : K -> K;
  q537618_fadd_assoc :
    forall a b c : K,
      q537618_fadd a (q537618_fadd b c) =
      q537618_fadd (q537618_fadd a b) c;
  q537618_fadd_comm :
    forall a b : K, q537618_fadd a b = q537618_fadd b a;
  q537618_fadd_zero :
    forall a : K, q537618_fadd a q537618_fzero = a;
  q537618_fadd_neg :
    forall a : K, q537618_fadd a (q537618_fneg a) = q537618_fzero;
  q537618_fmul_assoc :
    forall a b c : K,
      q537618_fmul a (q537618_fmul b c) =
      q537618_fmul (q537618_fmul a b) c;
  q537618_fmul_comm :
    forall a b : K, q537618_fmul a b = q537618_fmul b a;
  q537618_fmul_one :
    forall a : K, q537618_fmul a q537618_fone = a;
  q537618_fmul_inv :
    forall a : K,
      a <> q537618_fzero ->
      q537618_fmul a (q537618_finv a) = q537618_fone;
  q537618_fdistrib :
    forall a b c : K,
      q537618_fmul a (q537618_fadd b c) =
      q537618_fadd
        (q537618_fmul a b) (q537618_fmul a c);
  q537618_fzero_neq_one :
    q537618_fzero <> q537618_fone;
  q537618_fnorm : K -> R;
  q537618_fnorm_nonnegative :
    forall a : K, 0 <= q537618_fnorm a;
  q537618_fnorm_eq_zero :
    forall a : K,
      q537618_fnorm a = 0 <-> a = q537618_fzero;
  q537618_fnorm_add :
    forall a b : K,
      q537618_fnorm (q537618_fadd a b) <=
      q537618_fnorm a + q537618_fnorm b;
  q537618_fnorm_mul :
    forall a b : K,
      q537618_fnorm (q537618_fmul a b) =
      q537618_fnorm a * q537618_fnorm b;
  q537618_fnorm_one :
    q537618_fnorm q537618_fone = 1;
  q537618_fnorm_neg :
    forall a : K,
      q537618_fnorm (q537618_fneg a) = q537618_fnorm a;
  q537618_fnorm_nontrivial :
    exists a : K, 1 < q537618_fnorm a
}.

Arguments q537618_fzero {K} _.
Arguments q537618_fone {K} _.
Arguments q537618_fadd {K} _ _ _.
Arguments q537618_fmul {K} _ _ _.
Arguments q537618_fneg {K} _ _.
Arguments q537618_finv {K} _ _.
Arguments q537618_fnorm {K} _ _.

Definition q537618_fsub
    {K : Type}
    (scalar : q537618_normed_field K)
    (a b : K) : K :=
  q537618_fadd scalar a (q537618_fneg scalar b).

Definition q537618_fdist
    {K : Type}
    (scalar : q537618_normed_field K)
    (a b : K) : R :=
  q537618_fnorm scalar (q537618_fsub scalar a b).

Record q537618_seminormed_space
    (K E : Type)
    (scalar : q537618_normed_field K) : Type := {
  q537618_vzero : E;
  q537618_vadd : E -> E -> E;
  q537618_vneg : E -> E;
  q537618_smul : K -> E -> E;
  q537618_vadd_assoc :
    forall x y z : E,
      q537618_vadd x (q537618_vadd y z) =
      q537618_vadd (q537618_vadd x y) z;
  q537618_vadd_comm :
    forall x y : E, q537618_vadd x y = q537618_vadd y x;
  q537618_vadd_zero :
    forall x : E, q537618_vadd x q537618_vzero = x;
  q537618_vadd_neg :
    forall x : E, q537618_vadd x (q537618_vneg x) = q537618_vzero;
  q537618_smul_one :
    forall x : E,
      q537618_smul (q537618_fone scalar) x = x;
  q537618_smul_mul :
    forall (a b : K) (x : E),
      q537618_smul (q537618_fmul scalar a b) x =
      q537618_smul a (q537618_smul b x);
  q537618_smul_add_scalar :
    forall (a b : K) (x : E),
      q537618_smul (q537618_fadd scalar a b) x =
      q537618_vadd
        (q537618_smul a x) (q537618_smul b x);
  q537618_smul_add_vector :
    forall (a : K) (x y : E),
      q537618_smul a (q537618_vadd x y) =
      q537618_vadd
        (q537618_smul a x) (q537618_smul a y);
  q537618_smul_zero_scalar :
    forall x : E,
      q537618_smul (q537618_fzero scalar) x = q537618_vzero;
  q537618_smul_zero_vector :
    forall a : K,
      q537618_smul a q537618_vzero = q537618_vzero;
  q537618_vnorm : E -> R;
  q537618_vnorm_nonnegative :
    forall x : E, 0 <= q537618_vnorm x;
  q537618_vnorm_zero :
    q537618_vnorm q537618_vzero = 0;
  q537618_vnorm_neg :
    forall x : E, q537618_vnorm (q537618_vneg x) = q537618_vnorm x;
  q537618_vnorm_add :
    forall x y : E,
      q537618_vnorm (q537618_vadd x y) <=
      q537618_vnorm x + q537618_vnorm y;
  q537618_vnorm_smul :
    forall (a : K) (x : E),
      q537618_vnorm (q537618_smul a x) =
      q537618_fnorm scalar a * q537618_vnorm x
}.

Arguments q537618_vzero {K E scalar} _.
Arguments q537618_vadd {K E scalar} _ _ _.
Arguments q537618_vneg {K E scalar} _ _.
Arguments q537618_smul {K E scalar} _ _ _.
Arguments q537618_vnorm {K E scalar} _ _.

Definition q537618_vsub
    {K E : Type}
    {scalar : q537618_normed_field K}
    (space : @q537618_seminormed_space K E scalar)
    (x y : E) : E :=
  q537618_vadd space x (q537618_vneg space y).

Definition q537618_vdist
    {K E : Type}
    {scalar : q537618_normed_field K}
    (space : @q537618_seminormed_space K E scalar)
    (x y : E) : R :=
  q537618_vnorm space (q537618_vsub space x y).

Definition q537618_metric_open
    {X : Type}
    (distance : X -> X -> R)
    (U : q537618_set X) : Prop :=
  forall x : X,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : X, distance y x < radius -> U y.

Definition q537618_is_compact
    {X : Type}
    (is_open : q537618_set (q537618_set X))
    (S : q537618_set X) : Prop :=
  forall cover : q537618_set (q537618_set X),
    (forall U : q537618_set X,
      cover U -> is_open U) ->
    (forall x : X,
      S x ->
      exists U : q537618_set X, cover U /\ U x) ->
    exists finite_cover : list (q537618_set X),
      Forall cover finite_cover /\
      forall x : X,
        S x ->
        exists U : q537618_set X,
          In U finite_cover /\ U x.

Definition q537618_scalar_open
    {K : Type}
    (scalar : q537618_normed_field K) :
    q537618_set (q537618_set K) :=
  q537618_metric_open (q537618_fdist scalar).

Definition q537618_vector_open
    {K E : Type}
    {scalar : q537618_normed_field K}
    (space : @q537618_seminormed_space K E scalar) :
    q537618_set (q537618_set E) :=
  q537618_metric_open (q537618_vdist space).

Definition q537618_closed_ball
    {K : Type}
    (scalar : q537618_normed_field K)
    (center : K)
    (radius : R) : q537618_set K :=
  fun x : K => q537618_fdist scalar x center <= radius.

Definition q537618_proper_space
    {K : Type}
    (scalar : q537618_normed_field K) : Prop :=
  forall (center : K) (radius : R),
    q537618_is_compact
      (q537618_scalar_open scalar)
      (q537618_closed_ball scalar center radius).

Definition q537618_neighborhood
    {K E : Type}
    {scalar : q537618_normed_field K}
    (space : @q537618_seminormed_space K E scalar)
    (x : E)
    (S : q537618_set E) : Prop :=
  exists U : q537618_set E,
    q537618_vector_open space U /\
    U x /\
    forall y : E, U y -> S y.

Record q537618_weak_dual
    (K E : Type)
    (scalar : q537618_normed_field K)
    (space : @q537618_seminormed_space K E scalar) : Type := {
  q537618_dual_fun : E -> K;
  q537618_dual_add :
    forall x y : E,
      q537618_dual_fun (q537618_vadd space x y) =
      q537618_fadd scalar
        (q537618_dual_fun x) (q537618_dual_fun y);
  q537618_dual_smul :
    forall (a : K) (x : E),
      q537618_dual_fun (q537618_smul space a x) =
      q537618_fmul scalar a (q537618_dual_fun x);
  q537618_dual_continuous :
    forall (x : E) (epsilon : R),
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : E,
          q537618_vdist space y x < delta ->
          q537618_fdist scalar
            (q537618_dual_fun y)
            (q537618_dual_fun x) < epsilon
}.

Arguments q537618_dual_fun
  {K E scalar space} _ _.

Definition q537618_basic_weakstar_open
    {K E : Type}
    {scalar : q537618_normed_field K}
    {space : @q537618_seminormed_space K E scalar}
    (B : q537618_set (@q537618_weak_dual K E scalar space)) : Prop :=
  exists constraints : list (E * q537618_set K),
    (forall constraint : E * q537618_set K,
      In constraint constraints ->
      q537618_scalar_open scalar (snd constraint)) /\
    forall f : @q537618_weak_dual K E scalar space,
      B f <->
      forall constraint : E * q537618_set K,
        In constraint constraints ->
        (snd constraint)
          (q537618_dual_fun f (fst constraint)).

Definition q537618_weakstar_open
    {K E : Type}
    {scalar : q537618_normed_field K}
    {space : @q537618_seminormed_space K E scalar}
    (U : q537618_set (@q537618_weak_dual K E scalar space)) : Prop :=
  exists family :
      q537618_set
        (q537618_set (@q537618_weak_dual K E scalar space)),
    (forall B : q537618_set (@q537618_weak_dual K E scalar space),
      family B -> q537618_basic_weakstar_open B) /\
    forall f : @q537618_weak_dual K E scalar space,
      U f <->
      exists B : q537618_set (@q537618_weak_dual K E scalar space),
        family B /\ B f.

Definition q537618_polar
    {K E : Type}
    {scalar : q537618_normed_field K}
    {space : @q537618_seminormed_space K E scalar}
    (S : q537618_set E) :
    q537618_set (@q537618_weak_dual K E scalar space) :=
  fun f : @q537618_weak_dual K E scalar space =>
    forall x : E,
      S x ->
      q537618_fnorm scalar (q537618_dual_fun f x) <= 1.

Theorem q537618_banach_alaoglu :
  forall (K E : Type)
         (scalar : q537618_normed_field K)
         (space : @q537618_seminormed_space K E scalar),
    q537618_proper_space scalar ->
    forall S : q537618_set E,
      q537618_neighborhood
        space (q537618_vzero space) S ->
      q537618_is_compact
        (@q537618_weakstar_open K E scalar space)
        (q537618_polar S).
Admitted.
