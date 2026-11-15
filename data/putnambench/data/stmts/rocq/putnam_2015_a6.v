(* Statement-only formalization of PutnamBench corpus artifact putnam_2015_a6:
   determinant equality for intertwined positive-dimensional real square
   matrices with the same characteristic polynomial. This file contains no
   proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Reals Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2015_a6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_2015_a6_matrix_eq {n : nat}
    (A B : putnam_2015_a6_matrix n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Fixpoint putnam_2015_a6_fin_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2015_a6_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2015_a6_matrix_mul {n : nat}
    (A B : putnam_2015_a6_matrix n) :
    putnam_2015_a6_matrix n :=
  fun i j =>
    putnam_2015_a6_fin_sum n (fun k => A i k * B k j).

Definition putnam_2015_a6_matrix_sub {n : nat}
    (A B : putnam_2015_a6_matrix n) :
    putnam_2015_a6_matrix n :=
  fun i j => A i j - B i j.

Fixpoint putnam_2015_a6_fin_list
    (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | O => []
  | S k =>
      Fin.F1 :: map Fin.FS (putnam_2015_a6_fin_list k)
  end.

Definition putnam_2015_a6_rows
    {T : Type} (n : nat) (A : Fin.t n -> Fin.t n -> T) :
    list (list T) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2015_a6_fin_list n))
    (putnam_2015_a6_fin_list n).

Definition putnam_2015_a6_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2015_a6_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_2015_a6_real_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_2015_a6_real_sum rest
  end.

Fixpoint putnam_2015_a6_list_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_2015_a6_real_sum
            (map
              (fun j : nat =>
                putnam_2015_a6_cofactor_sign j *
                nth j row 0 *
                putnam_2015_a6_list_det k
                  (map (putnam_2015_a6_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2015_a6_determinant
    (n : nat) (A : putnam_2015_a6_matrix n) : R :=
  putnam_2015_a6_list_det n (putnam_2015_a6_rows n A).

Fixpoint putnam_2015_a6_poly_add
    (p q : list R) : list R :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' =>
      (a + b) :: putnam_2015_a6_poly_add p' q'
  end.

Fixpoint putnam_2015_a6_poly_scale
    (a : R) (p : list R) : list R :=
  match p with
  | [] => []
  | b :: rest => (a * b) :: putnam_2015_a6_poly_scale a rest
  end.

Fixpoint putnam_2015_a6_poly_mul
    (p q : list R) : list R :=
  match p with
  | [] => []
  | a :: rest =>
      putnam_2015_a6_poly_add
        (putnam_2015_a6_poly_scale a q)
        (0 :: putnam_2015_a6_poly_mul rest q)
  end.

Fixpoint putnam_2015_a6_poly_sum
    (ps : list (list R)) : list R :=
  match ps with
  | [] => []
  | p :: rest =>
      putnam_2015_a6_poly_add p (putnam_2015_a6_poly_sum rest)
  end.

Fixpoint putnam_2015_a6_poly_det
    (n : nat) (M : list (list (list R))) {struct n} : list R :=
  match n with
  | O => [1]
  | S k =>
      match M with
      | [] => []
      | row :: rows =>
          putnam_2015_a6_poly_sum
            (map
              (fun j : nat =>
                putnam_2015_a6_poly_scale
                  (putnam_2015_a6_cofactor_sign j)
                  (putnam_2015_a6_poly_mul
                    (nth j row [])
                    (putnam_2015_a6_poly_det k
                      (map (putnam_2015_a6_delete_nth j) rows))))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2015_a6_charpoly_entry {n : nat}
    (A : putnam_2015_a6_matrix n) (i j : Fin.t n) : list R :=
  if Fin.eq_dec i j
  then [- A i j; 1]
  else [- A i j].

Definition putnam_2015_a6_charpoly
    (n : nat) (A : putnam_2015_a6_matrix n) : list R :=
  putnam_2015_a6_poly_det n
    (putnam_2015_a6_rows n (putnam_2015_a6_charpoly_entry A)).

Definition putnam_2015_a6_charpoly_eq
    (n : nat) (A B : putnam_2015_a6_matrix n) : Prop :=
  forall k : nat,
    nth k (putnam_2015_a6_charpoly n A) 0 =
    nth k (putnam_2015_a6_charpoly n B) 0.

Theorem putnam_2015_a6
    (n : nat)
    (A B M : putnam_2015_a6_matrix n)
    (npos : (0 < n)%nat)
    (hmul :
      putnam_2015_a6_matrix_eq
        (putnam_2015_a6_matrix_mul A M)
        (putnam_2015_a6_matrix_mul M B))
    (hpoly : putnam_2015_a6_charpoly_eq n A B) :
  forall X : putnam_2015_a6_matrix n,
    putnam_2015_a6_determinant n
      (putnam_2015_a6_matrix_sub A
        (putnam_2015_a6_matrix_mul M X)) =
    putnam_2015_a6_determinant n
      (putnam_2015_a6_matrix_sub B
        (putnam_2015_a6_matrix_mul X M)).
Admitted.
