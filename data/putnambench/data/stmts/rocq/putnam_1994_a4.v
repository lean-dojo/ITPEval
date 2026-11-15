(* Statement-only formalization of PutnamBench corpus artifact putnam_1994_a4:
   invertibility over the integers of the first five matrices in an affine
   sequence of 2 by 2 matrices implies invertibility of the sixth; this file
   contains no proof. *)

From Stdlib Require Import ZArith Vectors.Fin.

Open Scope Z_scope.

Definition putnam_1994_a4_matrix : Type :=
  Fin.t 2 -> Fin.t 2 -> Z.

Definition putnam_1994_a4_matrix_eq
    (A B : putnam_1994_a4_matrix) : Prop :=
  forall i j, A i j = B i j.

Fixpoint putnam_1994_a4_fin_sum
    (n : nat) : (Fin.t n -> Z) -> Z :=
  match n as k return (Fin.t k -> Z) -> Z with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_1994_a4_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_1994_a4_add
    (A B : putnam_1994_a4_matrix) : putnam_1994_a4_matrix :=
  fun i j => A i j + B i j.

Definition putnam_1994_a4_scale
    (c : Z) (A : putnam_1994_a4_matrix) : putnam_1994_a4_matrix :=
  fun i j => c * A i j.

Definition putnam_1994_a4_mul
    (A B : putnam_1994_a4_matrix) : putnam_1994_a4_matrix :=
  fun i j =>
    putnam_1994_a4_fin_sum 2 (fun k => A i k * B k j).

Definition putnam_1994_a4_identity : putnam_1994_a4_matrix :=
  fun i j => if Fin.eq_dec i j then 1 else 0.

Definition putnam_1994_a4_invertible
    (A : putnam_1994_a4_matrix) : Prop :=
  exists Ainv : putnam_1994_a4_matrix,
    putnam_1994_a4_matrix_eq
      (putnam_1994_a4_mul A Ainv)
      putnam_1994_a4_identity /\
    putnam_1994_a4_matrix_eq
      (putnam_1994_a4_mul Ainv A)
      putnam_1994_a4_identity.

Theorem putnam_1994_a4
    (A B : putnam_1994_a4_matrix)
    (ABinv :
      putnam_1994_a4_invertible A /\
      putnam_1994_a4_invertible
        (putnam_1994_a4_add A B) /\
      putnam_1994_a4_invertible
        (putnam_1994_a4_add A (putnam_1994_a4_scale 2 B)) /\
      putnam_1994_a4_invertible
        (putnam_1994_a4_add A (putnam_1994_a4_scale 3 B)) /\
      putnam_1994_a4_invertible
        (putnam_1994_a4_add A (putnam_1994_a4_scale 4 B))) :
  putnam_1994_a4_invertible
    (putnam_1994_a4_add A (putnam_1994_a4_scale 5 B)).
Admitted.
