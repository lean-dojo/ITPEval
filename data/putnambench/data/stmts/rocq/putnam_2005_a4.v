(* Statement-only formalization of PutnamBench corpus artifact putnam_2005_a4:
   an all-ones submatrix of a square sign matrix with mutually orthogonal rows
   has area at most the matrix dimension. This file contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat Vectors.Fin.

Open Scope R_scope.

Definition putnam_2005_a4_matrix (rows cols : nat) : Type :=
  Fin.t rows -> Fin.t cols -> RbaseSymbolsImpl.R.

Fixpoint putnam_2005_a4_fin_sum
    (n : nat) :
    (Fin.t n -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R :=
  match n as m return
    (Fin.t m -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2005_a4_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2005_a4_row_inner_product
    {n : nat}
    (H : putnam_2005_a4_matrix n n)
    (i j : Fin.t n) : RbaseSymbolsImpl.R :=
  putnam_2005_a4_fin_sum n (fun k => H i k * H j k).

Theorem putnam_2005_a4
    (n : nat)
    (H : putnam_2005_a4_matrix n n)
    (a b : nat)
    (S : putnam_2005_a4_matrix a b)
    (npos : (1 <= n)%nat)
    (Hentries :
      forall i j : Fin.t n,
        H i j = 1 \/ H i j = -1)
    (Hortho :
      forall i j : Fin.t n,
        i <> j ->
        putnam_2005_a4_row_inner_product H i j = 0)
    (hab :
      (1 <= a)%nat /\
      (a <= n)%nat /\
      (1 <= b)%nat /\
      (b <= n)%nat)
    (Ssub :
      exists (rri : Fin.t a -> Fin.t n)
             (cri : Fin.t b -> Fin.t n),
        (forall i j : Fin.t a, rri i = rri j -> i = j) /\
        (forall i j : Fin.t b, cri i = cri j -> i = j) /\
        (forall (i : Fin.t a) (j : Fin.t b),
          S i j = H (rri i) (cri j)))
    (Sentries :
      forall (i : Fin.t a) (j : Fin.t b),
        S i j = 1) :
  (a * b <= n)%nat.
Admitted.
