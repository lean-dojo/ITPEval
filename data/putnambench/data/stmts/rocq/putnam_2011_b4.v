(* Statement-only formalization of PutnamBench corpus artifact putnam_2011_b4:
   the determinant of the complex tournament standings matrix is a
   nonnegative integer divisible by 2^2010. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2011_b4_complex : Type := (R * R)%type.

Definition putnam_2011_b4_czero : putnam_2011_b4_complex :=
  (0, 0).

Definition putnam_2011_b4_cone : putnam_2011_b4_complex :=
  (1, 0).

Definition putnam_2011_b4_ci : putnam_2011_b4_complex :=
  (0, 1).

Definition putnam_2011_b4_cadd
    (z w : putnam_2011_b4_complex) : putnam_2011_b4_complex :=
  (fst z + fst w, snd z + snd w).

Definition putnam_2011_b4_copp
    (z : putnam_2011_b4_complex) : putnam_2011_b4_complex :=
  (- fst z, - snd z).

Definition putnam_2011_b4_csub
    (z w : putnam_2011_b4_complex) : putnam_2011_b4_complex :=
  putnam_2011_b4_cadd z (putnam_2011_b4_copp w).

Definition putnam_2011_b4_cmul
    (z w : putnam_2011_b4_complex) : putnam_2011_b4_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition putnam_2011_b4_of_nat
    (n : nat) : putnam_2011_b4_complex :=
  (INR n, 0).

Definition putnam_2011_b4_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> putnam_2011_b4_complex.

Definition putnam_2011_b4_matrix_add
    {n : nat}
    (A B : putnam_2011_b4_matrix n) :
    putnam_2011_b4_matrix n :=
  fun i j => putnam_2011_b4_cadd (A i j) (B i j).

Definition putnam_2011_b4_matrix_smul
    {n : nat}
    (z : putnam_2011_b4_complex)
    (A : putnam_2011_b4_matrix n) :
    putnam_2011_b4_matrix n :=
  fun i j => putnam_2011_b4_cmul z (A i j).

Fixpoint putnam_2011_b4_indices
    (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S k => Fin.F1 :: map Fin.FS (putnam_2011_b4_indices k)
  end.

Definition putnam_2011_b4_matrix_rows
    {n : nat}
    (A : putnam_2011_b4_matrix n) :
    list (list putnam_2011_b4_complex) :=
  map
    (fun i =>
      map (fun j => A i j) (putnam_2011_b4_indices n))
    (putnam_2011_b4_indices n).

Fixpoint putnam_2011_b4_csum
    (zs : list putnam_2011_b4_complex) :
    putnam_2011_b4_complex :=
  match zs with
  | [] => putnam_2011_b4_czero
  | z :: rest =>
      putnam_2011_b4_cadd z (putnam_2011_b4_csum rest)
  end.

Definition putnam_2011_b4_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_2011_b4_cofactor_sign
    (j : nat) : putnam_2011_b4_complex :=
  if Nat.even j
  then putnam_2011_b4_cone
  else ((-1)%R, 0%R).

Fixpoint putnam_2011_b4_det
    (n : nat)
    (M : list (list putnam_2011_b4_complex))
    {struct n} : putnam_2011_b4_complex :=
  match n with
  | O => putnam_2011_b4_cone
  | S k =>
      match M with
      | [] => putnam_2011_b4_czero
      | row :: rows =>
          putnam_2011_b4_csum
            (map
              (fun j =>
                putnam_2011_b4_cmul
                  (putnam_2011_b4_cmul
                    (putnam_2011_b4_cofactor_sign j)
                    (nth j row putnam_2011_b4_czero))
                  (putnam_2011_b4_det k
                    (map
                      (putnam_2011_b4_delete_nth j)
                      rows)))
              (seq 0 (S k)))
      end
  end.

Definition putnam_2011_b4_determinant
    {n : nat}
    (A : putnam_2011_b4_matrix n) :
    putnam_2011_b4_complex :=
  putnam_2011_b4_det n (putnam_2011_b4_matrix_rows A).

Definition putnam_2011_b4_count
    {n : nat}
    (p : Fin.t n -> bool) : nat :=
  fold_right
    (fun i total => if p i then S total else total)
    O
    (putnam_2011_b4_indices n).

Definition putnam_2011_b4_tie_matrix
    (games : Fin.t 2011 -> Fin.t 2011 -> bool) :
    putnam_2011_b4_matrix 2011 :=
  fun h k =>
    putnam_2011_b4_of_nat
      (putnam_2011_b4_count
        (fun g => Bool.eqb (games g h) (games g k))).

Definition putnam_2011_b4_win_loss_matrix
    (games : Fin.t 2011 -> Fin.t 2011 -> bool) :
    putnam_2011_b4_matrix 2011 :=
  fun h k =>
    putnam_2011_b4_csub
      (putnam_2011_b4_of_nat
        (putnam_2011_b4_count
          (fun g =>
            andb (games g h) (negb (games g k)))))
      (putnam_2011_b4_of_nat
        (putnam_2011_b4_count
          (fun g =>
            andb (negb (games g h)) (games g k)))).

Theorem putnam_2011_b4
    (games : Fin.t 2011 -> Fin.t 2011 -> bool)
    (T W : putnam_2011_b4_matrix 2011)
    (hT : T = putnam_2011_b4_tie_matrix games)
    (hW : W = putnam_2011_b4_win_loss_matrix games) :
  exists n : nat,
    putnam_2011_b4_determinant
      (putnam_2011_b4_matrix_add
        T
        (putnam_2011_b4_matrix_smul putnam_2011_b4_ci W)) =
      putnam_2011_b4_of_nat n /\
    Nat.divide (Nat.pow 2 2010) n.
Admitted.
