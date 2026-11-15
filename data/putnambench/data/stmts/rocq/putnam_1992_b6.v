(* Statement-only formalization of PutnamBench corpus artifact putnam_1992_b6:
   a set of real square matrices satisfying signed-product closure and
   commute-or-anticommute conditions has cardinality at most n squared.
   This file contains no proof. *)

From Stdlib Require Import Reals Vectors.Fin Vectors.Vector Ensembles
  Finite_sets Arith.PeanoNat.

Open Scope R_scope.

Fixpoint putnam_1992_b6_vector_of_fn
    {A : Type} (n : nat) : (Fin.t n -> A) -> Vector.t A n :=
  match n as m return (Fin.t m -> A) -> Vector.t A m with
  | O => fun _ => Vector.nil A
  | S k =>
      fun f =>
        Vector.cons A (f Fin.F1) k
          (putnam_1992_b6_vector_of_fn k (fun i => f (Fin.FS i)))
  end.

Fixpoint putnam_1992_b6_fin_sum
    (n : nat) :
    (Fin.t n -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R :=
  match n as m return
    (Fin.t m -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_1992_b6_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_1992_b6_matrix (n : nat) : Type :=
  Vector.t (Vector.t RbaseSymbolsImpl.R n) n.

Definition putnam_1992_b6_matrix_of_fn
    (n : nat)
    (f : Fin.t n -> Fin.t n -> RbaseSymbolsImpl.R) :
    putnam_1992_b6_matrix n :=
  putnam_1992_b6_vector_of_fn n
    (fun i => putnam_1992_b6_vector_of_fn n (f i)).

Definition putnam_1992_b6_entry
    {n : nat} (A : putnam_1992_b6_matrix n)
    (i j : Fin.t n) : RbaseSymbolsImpl.R :=
  Vector.nth (Vector.nth A i) j.

Definition putnam_1992_b6_identity
    (n : nat) : putnam_1992_b6_matrix n :=
  putnam_1992_b6_matrix_of_fn n
    (fun i j => if Fin.eq_dec i j then 1 else 0).

Definition putnam_1992_b6_neg
    {n : nat} (A : putnam_1992_b6_matrix n) :
    putnam_1992_b6_matrix n :=
  putnam_1992_b6_matrix_of_fn n
    (fun i j => - putnam_1992_b6_entry A i j).

Definition putnam_1992_b6_mul
    {n : nat} (A B : putnam_1992_b6_matrix n) :
    putnam_1992_b6_matrix n :=
  putnam_1992_b6_matrix_of_fn n
    (fun i j =>
      putnam_1992_b6_fin_sum n
        (fun k =>
          putnam_1992_b6_entry A i k *
          putnam_1992_b6_entry B k j)).

Theorem putnam_1992_b6
    (n : nat)
    (npos : (0 < n)%nat)
    (M : Ensemble (putnam_1992_b6_matrix n))
    (h1 : M (putnam_1992_b6_identity n))
    (h2 :
      forall A B : putnam_1992_b6_matrix n,
        M A ->
        M B ->
        (M (putnam_1992_b6_mul A B) /\
         ~ M (putnam_1992_b6_neg (putnam_1992_b6_mul A B))) \/
        (~ M (putnam_1992_b6_mul A B) /\
         M (putnam_1992_b6_neg (putnam_1992_b6_mul A B))))
    (h3 :
      forall A B : putnam_1992_b6_matrix n,
        M A ->
        M B ->
        putnam_1992_b6_mul A B = putnam_1992_b6_mul B A \/
        putnam_1992_b6_mul A B =
          putnam_1992_b6_neg (putnam_1992_b6_mul B A))
    (h4 :
      forall A : putnam_1992_b6_matrix n,
        M A ->
        A <> putnam_1992_b6_identity n ->
        exists B : putnam_1992_b6_matrix n,
          M B /\
          putnam_1992_b6_mul A B =
            putnam_1992_b6_neg (putnam_1992_b6_mul B A)) :
  exists k : nat,
    cardinal (putnam_1992_b6_matrix n) M k /\
    (k <= Nat.pow n 2)%nat.
Admitted.
