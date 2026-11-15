(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226625
  (thousand-theorems__rocq__Q2226625), "Commandino's theorem": for a
  positive-dimensional simplex in an affine space over a characteristic-zero
  division ring, the vertex-to-centroid vector is the dimension scalar times
  the centroid-to-opposite-face-centroid vector. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Inductive q2226625_fin : nat -> Type :=
| q2226625_fzero : forall n : nat, q2226625_fin (S n)
| q2226625_fsucc :
    forall n : nat, q2226625_fin n -> q2226625_fin (S n).

Arguments q2226625_fzero {n}.
Arguments q2226625_fsucc {n} _.

Fixpoint q2226625_fin_sum
    {A : Type}
    (add : A -> A -> A)
    (zero : A)
    (n : nat) : (q2226625_fin n -> A) -> A :=
  match n as m return (q2226625_fin m -> A) -> A with
  | O => fun _ => zero
  | S m =>
      fun f =>
        add
          (f q2226625_fzero)
          (@q2226625_fin_sum A add zero m
            (fun i => f (q2226625_fsucc i)))
  end.

Fixpoint q2226625_fin_sum_except
    {A : Type}
    (add : A -> A -> A)
    (zero : A)
    (n : nat)
    (i : q2226625_fin n) :
    (q2226625_fin n -> A) -> A :=
  match i in q2226625_fin m
        return (q2226625_fin m -> A) -> A with
  | @q2226625_fzero m =>
      fun f =>
        @q2226625_fin_sum A add zero m
          (fun j => f (q2226625_fsucc j))
  | @q2226625_fsucc m i' =>
      fun f =>
        add
          (f q2226625_fzero)
          (@q2226625_fin_sum_except A add zero m i'
            (fun j => f (q2226625_fsucc j)))
  end.

Record q2226625_division_ring (K : Type) : Type := {
  q2226625_zero : K;
  q2226625_one : K;
  q2226625_add : K -> K -> K;
  q2226625_mul : K -> K -> K;
  q2226625_neg : K -> K;
  q2226625_inv : K -> K;

  q2226625_zero_ne_one :
    q2226625_zero <> q2226625_one;
  q2226625_add_assoc :
    forall x y z : K,
      q2226625_add x (q2226625_add y z) =
      q2226625_add (q2226625_add x y) z;
  q2226625_add_comm :
    forall x y : K, q2226625_add x y = q2226625_add y x;
  q2226625_add_zero :
    forall x : K, q2226625_add x q2226625_zero = x;
  q2226625_zero_add :
    forall x : K, q2226625_add q2226625_zero x = x;
  q2226625_add_neg :
    forall x : K, q2226625_add x (q2226625_neg x) = q2226625_zero;
  q2226625_neg_add :
    forall x : K, q2226625_add (q2226625_neg x) x = q2226625_zero;

  q2226625_mul_assoc :
    forall x y z : K,
      q2226625_mul x (q2226625_mul y z) =
      q2226625_mul (q2226625_mul x y) z;
  q2226625_mul_one :
    forall x : K, q2226625_mul x q2226625_one = x;
  q2226625_one_mul :
    forall x : K, q2226625_mul q2226625_one x = x;
  q2226625_mul_zero :
    forall x : K, q2226625_mul x q2226625_zero = q2226625_zero;
  q2226625_zero_mul :
    forall x : K, q2226625_mul q2226625_zero x = q2226625_zero;
  q2226625_left_distrib :
    forall x y z : K,
      q2226625_mul x (q2226625_add y z) =
      q2226625_add (q2226625_mul x y) (q2226625_mul x z);
  q2226625_right_distrib :
    forall x y z : K,
      q2226625_mul (q2226625_add x y) z =
      q2226625_add (q2226625_mul x z) (q2226625_mul y z);

  q2226625_inv_zero :
    q2226625_inv q2226625_zero = q2226625_zero;
  q2226625_mul_inv :
    forall x : K,
      x <> q2226625_zero ->
      q2226625_mul x (q2226625_inv x) = q2226625_one;
  q2226625_inv_mul :
    forall x : K,
      x <> q2226625_zero ->
      q2226625_mul (q2226625_inv x) x = q2226625_one
}.

Arguments q2226625_zero {K} _.
Arguments q2226625_one {K} _.
Arguments q2226625_add {K} _ _ _.
Arguments q2226625_mul {K} _ _ _.
Arguments q2226625_neg {K} _ _.
Arguments q2226625_inv {K} _ _.

Fixpoint q2226625_nat_cast
    {K : Type}
    (F : q2226625_division_ring K)
    (n : nat) : K :=
  match n with
  | O => q2226625_zero F
  | S m =>
      q2226625_add F (q2226625_nat_cast F m) (q2226625_one F)
  end.

Definition q2226625_char_zero
    {K : Type}
    (F : q2226625_division_ring K) : Prop :=
  forall m n : nat,
    q2226625_nat_cast F m = q2226625_nat_cast F n ->
    m = n.

Record q2226625_module
    (K V : Type)
    (F : q2226625_division_ring K) : Type := {
  q2226625_vec_zero : V;
  q2226625_vec_add : V -> V -> V;
  q2226625_vec_neg : V -> V;
  q2226625_smul : K -> V -> V;

  q2226625_vec_add_assoc :
    forall x y z : V,
      q2226625_vec_add x (q2226625_vec_add y z) =
      q2226625_vec_add (q2226625_vec_add x y) z;
  q2226625_vec_add_comm :
    forall x y : V, q2226625_vec_add x y = q2226625_vec_add y x;
  q2226625_vec_add_zero :
    forall x : V, q2226625_vec_add x q2226625_vec_zero = x;
  q2226625_vec_zero_add :
    forall x : V, q2226625_vec_add q2226625_vec_zero x = x;
  q2226625_vec_add_neg :
    forall x : V,
      q2226625_vec_add x (q2226625_vec_neg x) = q2226625_vec_zero;
  q2226625_vec_neg_add :
    forall x : V,
      q2226625_vec_add (q2226625_vec_neg x) x = q2226625_vec_zero;

  q2226625_one_smul :
    forall x : V, q2226625_smul (q2226625_one F) x = x;
  q2226625_mul_smul :
    forall (a b : K) (x : V),
      q2226625_smul (q2226625_mul F a b) x =
      q2226625_smul a (q2226625_smul b x);
  q2226625_add_smul :
    forall (a b : K) (x : V),
      q2226625_smul (q2226625_add F a b) x =
      q2226625_vec_add
        (q2226625_smul a x) (q2226625_smul b x);
  q2226625_smul_add :
    forall (a : K) (x y : V),
      q2226625_smul a (q2226625_vec_add x y) =
      q2226625_vec_add
        (q2226625_smul a x) (q2226625_smul a y);
  q2226625_zero_smul :
    forall x : V,
      q2226625_smul (q2226625_zero F) x = q2226625_vec_zero;
  q2226625_smul_zero :
    forall a : K, q2226625_smul a q2226625_vec_zero = q2226625_vec_zero
}.

Arguments q2226625_vec_zero {K V F} _.
Arguments q2226625_vec_add {K V F} _ _ _.
Arguments q2226625_vec_neg {K V F} _ _.
Arguments q2226625_smul {K V F} _ _ _.

Record q2226625_affine_space
    (K V P : Type)
    (F : q2226625_division_ring K)
    (M : @q2226625_module K V F) : Type := {
  q2226625_point_vadd : V -> P -> P;
  q2226625_point_vsub : P -> P -> V;
  q2226625_zero_vadd :
    forall p : P,
      q2226625_point_vadd (q2226625_vec_zero M) p = p;
  q2226625_add_vadd :
    forall (x y : V) (p : P),
      q2226625_point_vadd (q2226625_vec_add M x y) p =
      q2226625_point_vadd x (q2226625_point_vadd y p);
  q2226625_vsub_vadd :
    forall (x : V) (p : P),
      q2226625_point_vsub (q2226625_point_vadd x p) p = x;
  q2226625_vadd_vsub :
    forall p q : P,
      q2226625_point_vadd (q2226625_point_vsub p q) q = p
}.

Arguments q2226625_point_vadd {K V P F M} _ _ _.
Arguments q2226625_point_vsub {K V P F M} _ _ _.

Definition q2226625_affine_independent
    {K V P : Type}
    {F : q2226625_division_ring K}
    {M : @q2226625_module K V F}
    (A : @q2226625_affine_space K V P F M)
    (n : nat)
    (points : q2226625_fin (S n) -> P) : Prop :=
  forall coefficients : q2226625_fin (S n) -> K,
    @q2226625_fin_sum K
      (q2226625_add F) (q2226625_zero F) (S n) coefficients =
      q2226625_zero F ->
    @q2226625_fin_sum V
      (q2226625_vec_add M) (q2226625_vec_zero M) (S n)
      (fun j =>
        q2226625_smul M (coefficients j)
          (q2226625_point_vsub A
            (points j) (points q2226625_fzero))) =
      q2226625_vec_zero M ->
    forall j : q2226625_fin (S n),
      coefficients j = q2226625_zero F.

Record q2226625_simplex
    (K V P : Type)
    (F : q2226625_division_ring K)
    (M : @q2226625_module K V F)
    (A : @q2226625_affine_space K V P F M)
    (n : nat) : Type := {
  q2226625_points : q2226625_fin (S n) -> P;
  q2226625_independent :
    @q2226625_affine_independent K V P F M
      A n q2226625_points
}.

Arguments q2226625_points {K V P F M A n} _ _.

Definition q2226625_centroid
    {K V P : Type}
    {F : q2226625_division_ring K}
    {M : @q2226625_module K V F}
    (A : @q2226625_affine_space K V P F M)
    (n : nat)
    (points : q2226625_fin (S n) -> P) : P :=
  q2226625_point_vadd A
    (q2226625_smul M
      (q2226625_inv F (q2226625_nat_cast F (S n)))
      (@q2226625_fin_sum V
        (q2226625_vec_add M) (q2226625_vec_zero M) (S n)
        (fun j =>
          q2226625_point_vsub A
            (points j) (points q2226625_fzero))))
    (points q2226625_fzero).

Definition q2226625_face_opposite_centroid
    {K V P : Type}
    {F : q2226625_division_ring K}
    {M : @q2226625_module K V F}
    (A : @q2226625_affine_space K V P F M)
    (n : nat)
    (points : q2226625_fin (S n) -> P)
    (i : q2226625_fin (S n)) : P :=
  q2226625_point_vadd A
    (q2226625_smul M
      (q2226625_inv F (q2226625_nat_cast F n))
      (@q2226625_fin_sum_except V
        (q2226625_vec_add M) (q2226625_vec_zero M) (S n) i
        (fun j =>
          q2226625_point_vsub A (points j) (points i))))
    (points i).

Theorem q2226625_point_vsub_centroid_eq_smul_vsub :
  forall (K V P : Type)
         (F : q2226625_division_ring K)
         (M : @q2226625_module K V F)
         (A : @q2226625_affine_space K V P F M)
         (n : nat),
    n <> O ->
    q2226625_char_zero F ->
    forall (s : @q2226625_simplex K V P F M A n)
           (i : q2226625_fin (S n)),
      q2226625_point_vsub A
        (q2226625_points s i)
        (@q2226625_centroid K V P F M
          A n (q2226625_points s)) =
      q2226625_smul M (q2226625_nat_cast F n)
        (q2226625_point_vsub A
          (@q2226625_centroid K V P F M
            A n (q2226625_points s))
          (@q2226625_face_opposite_centroid K V P F M
            A n (q2226625_points s) i)).
Admitted.
