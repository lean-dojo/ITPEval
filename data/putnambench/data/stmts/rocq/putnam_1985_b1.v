(* Statement-only formalization of PutnamBench artifact putnam_1985_b1:
   the five distinct integer roots -2, -1, 0, 1, 2 minimize the number of
   nonzero coefficients in their monic real quintic. This file contains no
   proof. *)

From Stdlib Require Import Reals ZArith Lists.List.

Open Scope R_scope.

Record putnam_1985_b1_roots : Type := {
  putnam_1985_b1_m1 : Z;
  putnam_1985_b1_m2 : Z;
  putnam_1985_b1_m3 : Z;
  putnam_1985_b1_m4 : Z;
  putnam_1985_b1_m5 : Z
}.

Definition putnam_1985_b1_distinct
    (m : putnam_1985_b1_roots) : Prop :=
  putnam_1985_b1_m1 m <> putnam_1985_b1_m2 m /\
  putnam_1985_b1_m1 m <> putnam_1985_b1_m3 m /\
  putnam_1985_b1_m1 m <> putnam_1985_b1_m4 m /\
  putnam_1985_b1_m1 m <> putnam_1985_b1_m5 m /\
  putnam_1985_b1_m2 m <> putnam_1985_b1_m3 m /\
  putnam_1985_b1_m2 m <> putnam_1985_b1_m4 m /\
  putnam_1985_b1_m2 m <> putnam_1985_b1_m5 m /\
  putnam_1985_b1_m3 m <> putnam_1985_b1_m4 m /\
  putnam_1985_b1_m3 m <> putnam_1985_b1_m5 m /\
  putnam_1985_b1_m4 m <> putnam_1985_b1_m5 m.

Definition putnam_1985_b1_linear_factor (root : Z) : list R :=
  (- IZR root) :: 1 :: nil.

Fixpoint putnam_1985_b1_poly_add
    (p q : list R) : list R :=
  match p, q with
  | nil, q' => q'
  | p', nil => p'
  | a :: p', b :: q' =>
      (a + b) :: putnam_1985_b1_poly_add p' q'
  end.

Fixpoint putnam_1985_b1_poly_scale
    (a : R) (p : list R) : list R :=
  match p with
  | nil => nil
  | b :: p' => (a * b) :: putnam_1985_b1_poly_scale a p'
  end.

Fixpoint putnam_1985_b1_poly_mul
    (p q : list R) : list R :=
  match p with
  | nil => nil
  | a :: p' =>
      putnam_1985_b1_poly_add
        (putnam_1985_b1_poly_scale a q)
        (0 :: putnam_1985_b1_poly_mul p' q)
  end.

Definition putnam_1985_b1_polynomial
    (m : putnam_1985_b1_roots) : list R :=
  putnam_1985_b1_poly_mul
    (putnam_1985_b1_linear_factor (putnam_1985_b1_m1 m))
    (putnam_1985_b1_poly_mul
      (putnam_1985_b1_linear_factor (putnam_1985_b1_m2 m))
      (putnam_1985_b1_poly_mul
        (putnam_1985_b1_linear_factor (putnam_1985_b1_m3 m))
        (putnam_1985_b1_poly_mul
          (putnam_1985_b1_linear_factor (putnam_1985_b1_m4 m))
          (putnam_1985_b1_linear_factor (putnam_1985_b1_m5 m))))).

Fixpoint putnam_1985_b1_nonzero_coefficients
    (p : list R) : nat :=
  match p with
  | nil => O
  | a :: p' =>
      if Req_EM_T a 0
      then putnam_1985_b1_nonzero_coefficients p'
      else S (putnam_1985_b1_nonzero_coefficients p')
  end.

Definition putnam_1985_b1_solution : putnam_1985_b1_roots :=
  {| putnam_1985_b1_m1 := (-2)%Z;
     putnam_1985_b1_m2 := (-1)%Z;
     putnam_1985_b1_m3 := 0%Z;
     putnam_1985_b1_m4 := 1%Z;
     putnam_1985_b1_m5 := 2%Z |}.

Theorem putnam_1985_b1 :
  putnam_1985_b1_distinct putnam_1985_b1_solution /\
  forall m : putnam_1985_b1_roots,
    putnam_1985_b1_distinct m ->
    (putnam_1985_b1_nonzero_coefficients
       (putnam_1985_b1_polynomial putnam_1985_b1_solution) <=
     putnam_1985_b1_nonzero_coefficients
       (putnam_1985_b1_polynomial m))%nat.
Admitted.
