(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1420905
  (thousand-theorems__rocq__Q1420905), "Hilbert's theorem 90": in a
  finite-dimensional cyclic Galois field extension, every element of algebra
  norm one is a quotient y/g(y) for a nonzero y. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1420905_field (F : Type) : Type := {
  q1420905_zero : F;
  q1420905_one : F;
  q1420905_add : F -> F -> F;
  q1420905_mul : F -> F -> F;
  q1420905_neg : F -> F;
  q1420905_inv : F -> F;
  q1420905_add_assoc :
    forall x y z : F,
      q1420905_add x (q1420905_add y z) =
      q1420905_add (q1420905_add x y) z;
  q1420905_add_comm :
    forall x y : F,
      q1420905_add x y = q1420905_add y x;
  q1420905_add_zero :
    forall x : F,
      q1420905_add x q1420905_zero = x;
  q1420905_add_neg :
    forall x : F,
      q1420905_add x (q1420905_neg x) = q1420905_zero;
  q1420905_mul_assoc :
    forall x y z : F,
      q1420905_mul x (q1420905_mul y z) =
      q1420905_mul (q1420905_mul x y) z;
  q1420905_mul_comm :
    forall x y : F,
      q1420905_mul x y = q1420905_mul y x;
  q1420905_mul_one :
    forall x : F,
      q1420905_mul x q1420905_one = x;
  q1420905_left_distrib :
    forall x y z : F,
      q1420905_mul x (q1420905_add y z) =
      q1420905_add
        (q1420905_mul x y) (q1420905_mul x z);
  q1420905_mul_zero :
    forall x : F,
      q1420905_mul x q1420905_zero = q1420905_zero;
  q1420905_inv_zero :
    q1420905_inv q1420905_zero = q1420905_zero;
  q1420905_mul_inv :
    forall x : F,
      x <> q1420905_zero ->
      q1420905_mul x (q1420905_inv x) = q1420905_one;
  q1420905_zero_ne_one :
    q1420905_zero <> q1420905_one
}.

Arguments q1420905_zero {F} _.
Arguments q1420905_one {F} _.
Arguments q1420905_add {F} _ _ _.
Arguments q1420905_mul {F} _ _ _.
Arguments q1420905_neg {F} _ _.
Arguments q1420905_inv {F} _ _.

Record q1420905_field_algebra
    (K L : Type)
    (FK : q1420905_field K)
    (FL : q1420905_field L) : Type := {
  q1420905_embed : K -> L;
  q1420905_embed_zero :
    q1420905_embed (q1420905_zero FK) = q1420905_zero FL;
  q1420905_embed_one :
    q1420905_embed (q1420905_one FK) = q1420905_one FL;
  q1420905_embed_add :
    forall a b : K,
      q1420905_embed (q1420905_add FK a b) =
      q1420905_add FL (q1420905_embed a) (q1420905_embed b);
  q1420905_embed_mul :
    forall a b : K,
      q1420905_embed (q1420905_mul FK a b) =
      q1420905_mul FL (q1420905_embed a) (q1420905_embed b);
  q1420905_embed_injective :
    forall a b : K,
      q1420905_embed a = q1420905_embed b -> a = b
}.

Arguments q1420905_embed {K L FK FL} _ _.

Record q1420905_finite_type (I : Type) : Type := {
  q1420905_enum : list I;
  q1420905_enum_nodup : NoDup q1420905_enum;
  q1420905_enum_complete :
    forall i : I, In i q1420905_enum
}.

Arguments q1420905_enum {I} _.

Fixpoint q1420905_sum_list
    {I F : Type}
    (FF : q1420905_field F)
    (indices : list I)
    (term : I -> F) : F :=
  match indices with
  | nil => q1420905_zero FF
  | cons i rest =>
      q1420905_add FF
        (term i) (q1420905_sum_list FF rest term)
  end.

Definition q1420905_linear_combination
    {K L I : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL)
    (fin : q1420905_finite_type I)
    (basis : I -> L)
    (coefficients : I -> K) : L :=
  q1420905_sum_list FL (q1420905_enum fin)
    (fun i =>
      q1420905_mul FL
        (q1420905_embed A (coefficients i))
        (basis i)).

Definition q1420905_basis_data
    {K L I : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL)
    (fin : q1420905_finite_type I)
    (basis : I -> L)
    (coordinates : L -> I -> K) : Prop :=
  (forall x : L,
      q1420905_linear_combination A fin basis (coordinates x) = x) /\
  (forall (coefficients : I -> K) (i : I),
      coordinates
        (q1420905_linear_combination A fin basis coefficients) i =
      coefficients i).

Definition q1420905_finite_dimensional
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL) : Prop :=
  exists (I : Type)
         (fin : q1420905_finite_type I)
         (basis : I -> L)
         (coordinates : L -> I -> K),
    q1420905_basis_data A fin basis coordinates.

Fixpoint q1420905_determinant
    {I F : Type}
    (FF : q1420905_field F)
    (rows cols : list I)
    (M : I -> I -> F) {struct rows} : F :=
  match rows with
  | nil => q1420905_one FF
  | cons i remaining_rows =>
      let fix expand
          (prefix remaining_cols : list I)
          (positive : bool) {struct remaining_cols} : F :=
        match remaining_cols with
        | nil => q1420905_zero FF
        | cons j suffix =>
            let minor :=
              q1420905_determinant FF
                remaining_rows (rev prefix ++ suffix) M in
            let term := q1420905_mul FF (M i j) minor in
            q1420905_add FF
              (if positive then term else q1420905_neg FF term)
              (expand (cons j prefix) suffix (negb positive))
        end in
      expand nil cols true
  end.

Definition q1420905_norm_eq_one
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL)
    (x : L) : Prop :=
  exists (I : Type)
         (fin : q1420905_finite_type I)
         (basis : I -> L)
         (coordinates : L -> I -> K),
    q1420905_basis_data A fin basis coordinates /\
    q1420905_determinant FK
      (q1420905_enum fin)
      (q1420905_enum fin)
      (fun row column =>
        coordinates
          (q1420905_mul FL x (basis column)) row) =
    q1420905_one FK.

Record q1420905_alg_automorphism
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL) : Type := {
  q1420905_aut_apply : L -> L;
  q1420905_aut_inverse : L -> L;
  q1420905_aut_embed :
    forall a : K,
      q1420905_aut_apply (q1420905_embed A a) =
      q1420905_embed A a;
  q1420905_aut_add :
    forall x y : L,
      q1420905_aut_apply (q1420905_add FL x y) =
      q1420905_add FL
        (q1420905_aut_apply x) (q1420905_aut_apply y);
  q1420905_aut_mul :
    forall x y : L,
      q1420905_aut_apply (q1420905_mul FL x y) =
      q1420905_mul FL
        (q1420905_aut_apply x) (q1420905_aut_apply y);
  q1420905_aut_inverse_left :
    forall x : L,
      q1420905_aut_inverse (q1420905_aut_apply x) = x;
  q1420905_aut_inverse_right :
    forall x : L,
      q1420905_aut_apply (q1420905_aut_inverse x) = x
}.

Arguments q1420905_aut_apply {K L FK FL A} _ _.
Arguments q1420905_aut_inverse {K L FK FL A} _ _.

Fixpoint q1420905_iterate
    {X : Type} (f : X -> X) (n : nat) (x : X) : X :=
  match n with
  | O => x
  | S m => f (q1420905_iterate f m x)
  end.

Definition q1420905_generates_automorphisms
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    {A : @q1420905_field_algebra K L FK FL}
    (g : q1420905_alg_automorphism A) : Prop :=
  forall sigma : q1420905_alg_automorphism A,
    exists n : nat,
      (forall x : L,
          q1420905_aut_apply sigma x =
          q1420905_iterate (q1420905_aut_apply g) n x) \/
      (forall x : L,
          q1420905_aut_apply sigma x =
          q1420905_iterate (q1420905_aut_inverse g) n x).

Definition q1420905_is_cyclic
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL) : Prop :=
  exists g : q1420905_alg_automorphism A,
    q1420905_generates_automorphisms g.

Definition q1420905_is_galois
    {K L : Type}
    {FK : q1420905_field K}
    {FL : q1420905_field L}
    (A : @q1420905_field_algebra K L FK FL) : Prop :=
  forall x : L,
    (forall sigma : q1420905_alg_automorphism A,
        q1420905_aut_apply sigma x = x) ->
    exists a : K, q1420905_embed A a = x.

Theorem groupCohomology_exists_div_of_norm_eq_one :
  forall (K L : Type)
         (FK : q1420905_field K)
         (FL : q1420905_field L)
         (A : @q1420905_field_algebra K L FK FL),
    q1420905_finite_dimensional A ->
    q1420905_is_galois A ->
    q1420905_is_cyclic A ->
    forall g : q1420905_alg_automorphism A,
      q1420905_generates_automorphisms g ->
      forall x : L,
        q1420905_norm_eq_one A x ->
        exists y : L,
          y <> q1420905_zero FL /\
          q1420905_mul FL y
            (q1420905_inv FL (q1420905_aut_apply g y)) = x.
Admitted.
