(* Statement-only formalization of PutnamBench artifact putnam_1986_b6:
   square matrices over a field whose products A B^T and C D^T are symmetric
   and satisfy A D^T - B C^T = I also satisfy A^T D - C^T B = I. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.

Record putnam_1986_b6_field (F : Type) : Type := {
  putnam_1986_b6_zero : F;
  putnam_1986_b6_one : F;
  putnam_1986_b6_add : F -> F -> F;
  putnam_1986_b6_mul : F -> F -> F;
  putnam_1986_b6_opp : F -> F;
  putnam_1986_b6_inv : F -> F;
  putnam_1986_b6_add_assoc :
    forall x y z : F,
      putnam_1986_b6_add x (putnam_1986_b6_add y z) =
      putnam_1986_b6_add (putnam_1986_b6_add x y) z;
  putnam_1986_b6_add_comm :
    forall x y : F,
      putnam_1986_b6_add x y = putnam_1986_b6_add y x;
  putnam_1986_b6_add_zero_l :
    forall x : F,
      putnam_1986_b6_add putnam_1986_b6_zero x = x;
  putnam_1986_b6_add_opp_l :
    forall x : F,
      putnam_1986_b6_add (putnam_1986_b6_opp x) x =
      putnam_1986_b6_zero;
  putnam_1986_b6_mul_assoc :
    forall x y z : F,
      putnam_1986_b6_mul x (putnam_1986_b6_mul y z) =
      putnam_1986_b6_mul (putnam_1986_b6_mul x y) z;
  putnam_1986_b6_mul_comm :
    forall x y : F,
      putnam_1986_b6_mul x y = putnam_1986_b6_mul y x;
  putnam_1986_b6_mul_one_l :
    forall x : F,
      putnam_1986_b6_mul putnam_1986_b6_one x = x;
  putnam_1986_b6_mul_add_distr_l :
    forall x y z : F,
      putnam_1986_b6_mul x (putnam_1986_b6_add y z) =
      putnam_1986_b6_add
        (putnam_1986_b6_mul x y)
        (putnam_1986_b6_mul x z);
  putnam_1986_b6_one_neq_zero :
    putnam_1986_b6_one <> putnam_1986_b6_zero;
  putnam_1986_b6_inv_zero :
    putnam_1986_b6_inv putnam_1986_b6_zero =
    putnam_1986_b6_zero;
  putnam_1986_b6_inv_mul_cancel :
    forall x : F,
      x <> putnam_1986_b6_zero ->
      putnam_1986_b6_mul (putnam_1986_b6_inv x) x =
      putnam_1986_b6_one
}.

Arguments putnam_1986_b6_zero {F} _.
Arguments putnam_1986_b6_one {F} _.
Arguments putnam_1986_b6_add {F} _ _ _.
Arguments putnam_1986_b6_mul {F} _ _ _.
Arguments putnam_1986_b6_opp {F} _ _.

Definition putnam_1986_b6_matrix (F : Type) (n : nat) : Type :=
  Fin.t n -> Fin.t n -> F.

Fixpoint putnam_1986_b6_sum {F : Type}
    (zero : F) (add : F -> F -> F) (n : nat) :
    (Fin.t n -> F) -> F :=
  match n as m return (Fin.t m -> F) -> F with
  | O => fun _ => zero
  | S m =>
      fun f =>
        add (f Fin.F1)
          (putnam_1986_b6_sum zero add m
            (fun i : Fin.t m => f (Fin.FS i)))
  end.

Definition putnam_1986_b6_transpose {F : Type} {n : nat}
    (A : putnam_1986_b6_matrix F n) :
    putnam_1986_b6_matrix F n :=
  fun i j => A j i.

Definition putnam_1986_b6_matrix_mul {F : Type} {n : nat}
    (field : putnam_1986_b6_field F)
    (A B : putnam_1986_b6_matrix F n) :
    putnam_1986_b6_matrix F n :=
  fun i j =>
    putnam_1986_b6_sum
      (putnam_1986_b6_zero field)
      (putnam_1986_b6_add field)
      n
      (fun k => putnam_1986_b6_mul field (A i k) (B k j)).

Definition putnam_1986_b6_matrix_sub {F : Type} {n : nat}
    (field : putnam_1986_b6_field F)
    (A B : putnam_1986_b6_matrix F n) :
    putnam_1986_b6_matrix F n :=
  fun i j =>
    putnam_1986_b6_add field
      (A i j) (putnam_1986_b6_opp field (B i j)).

Definition putnam_1986_b6_identity {F : Type} {n : nat}
    (field : putnam_1986_b6_field F) :
    putnam_1986_b6_matrix F n :=
  fun i j =>
    if Fin.eq_dec i j
    then putnam_1986_b6_one field
    else putnam_1986_b6_zero field.

Definition putnam_1986_b6_matrix_eq {F : Type} {n : nat}
    (A B : putnam_1986_b6_matrix F n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Theorem putnam_1986_b6
    (n : nat)
    (npos : (0 < n)%nat)
    (F : Type)
    (field : putnam_1986_b6_field F)
    (A B C D : putnam_1986_b6_matrix F n)
    (hsymm_AB :
      putnam_1986_b6_matrix_eq
        (putnam_1986_b6_matrix_mul
          field A (putnam_1986_b6_transpose B))
        (putnam_1986_b6_transpose
          (putnam_1986_b6_matrix_mul
            field A (putnam_1986_b6_transpose B))))
    (hsymm_CD :
      putnam_1986_b6_matrix_eq
        (putnam_1986_b6_matrix_mul
          field C (putnam_1986_b6_transpose D))
        (putnam_1986_b6_transpose
          (putnam_1986_b6_matrix_mul
            field C (putnam_1986_b6_transpose D))))
    (hid :
      putnam_1986_b6_matrix_eq
        (putnam_1986_b6_matrix_sub field
          (putnam_1986_b6_matrix_mul
            field A (putnam_1986_b6_transpose D))
          (putnam_1986_b6_matrix_mul
            field B (putnam_1986_b6_transpose C)))
        (putnam_1986_b6_identity field)) :
  putnam_1986_b6_matrix_eq
    (putnam_1986_b6_matrix_sub field
      (putnam_1986_b6_matrix_mul
        field (putnam_1986_b6_transpose A) D)
      (putnam_1986_b6_matrix_mul
        field (putnam_1986_b6_transpose C) B))
    (putnam_1986_b6_identity field).
Admitted.
