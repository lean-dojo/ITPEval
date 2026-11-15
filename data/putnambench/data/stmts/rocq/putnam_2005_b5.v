(* Statement-only formalization of PutnamBench corpus artifact putnam_2005_b5:
   a real multivariate polynomial that is harmonic and divisible by the sum
   of the squares of its variables is identically zero. This file contains
   no proof. *)

From Stdlib Require Import Reals Lists.List Vectors.Fin Arith.PeanoNat.

Import ListNotations.
Open Scope R_scope.

Definition putnam_2005_b5_polynomial (n : nat) : Type :=
  list (RbaseSymbolsImpl.R * (Fin.t n -> nat)).

Fixpoint putnam_2005_b5_fin_product
    (n : nat) :
    (Fin.t n -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R :=
  match n as m return
    (Fin.t m -> RbaseSymbolsImpl.R) -> RbaseSymbolsImpl.R with
  | O => fun _ => 1
  | S k =>
      fun f =>
        f Fin.F1 *
        putnam_2005_b5_fin_product k (fun i => f (Fin.FS i))
  end.

Fixpoint putnam_2005_b5_fin_enum
    (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S k => Fin.F1 :: List.map Fin.FS (putnam_2005_b5_fin_enum k)
  end.

Fixpoint putnam_2005_b5_eval
    {n : nat}
    (P : putnam_2005_b5_polynomial n)
    (x : Fin.t n -> RbaseSymbolsImpl.R) : RbaseSymbolsImpl.R :=
  match P with
  | [] => 0
  | term :: rest =>
      fst term *
        putnam_2005_b5_fin_product n
          (fun i => x i ^ snd term i) +
      putnam_2005_b5_eval rest x
  end.

Definition putnam_2005_b5_polynomial_eq
    {n : nat}
    (P Q : putnam_2005_b5_polynomial n) : Prop :=
  forall x : Fin.t n -> RbaseSymbolsImpl.R,
    putnam_2005_b5_eval P x = putnam_2005_b5_eval Q x.

Definition putnam_2005_b5_zero
    (n : nat) : putnam_2005_b5_polynomial n :=
  [].

Definition putnam_2005_b5_term_mul
    {n : nat}
    (a b : RbaseSymbolsImpl.R * (Fin.t n -> nat)) :
    RbaseSymbolsImpl.R * (Fin.t n -> nat) :=
  (fst a * fst b,
   fun i => Nat.add (snd a i) (snd b i)).

Fixpoint putnam_2005_b5_mul_by_term
    {n : nat}
    (a : RbaseSymbolsImpl.R * (Fin.t n -> nat))
    (Q : putnam_2005_b5_polynomial n) :
    putnam_2005_b5_polynomial n :=
  match Q with
  | [] => []
  | b :: rest =>
      putnam_2005_b5_term_mul a b ::
      putnam_2005_b5_mul_by_term a rest
  end.

Fixpoint putnam_2005_b5_polynomial_mul
    {n : nat}
    (P Q : putnam_2005_b5_polynomial n) :
    putnam_2005_b5_polynomial n :=
  match P with
  | [] => []
  | a :: rest =>
      putnam_2005_b5_mul_by_term a Q ++
      putnam_2005_b5_polynomial_mul rest Q
  end.

Fixpoint putnam_2005_b5_partial_derivative
    {n : nat}
    (i : Fin.t n)
    (P : putnam_2005_b5_polynomial n) :
    putnam_2005_b5_polynomial n :=
  match P with
  | [] => []
  | term :: rest =>
      (fst term * INR (snd term i),
       fun j =>
         if Fin.eq_dec j i
         then Nat.pred (snd term j)
         else snd term j) ::
      putnam_2005_b5_partial_derivative i rest
  end.

Definition putnam_2005_b5_second_partial
    {n : nat}
    (i : Fin.t n)
    (P : putnam_2005_b5_polynomial n) :
    putnam_2005_b5_polynomial n :=
  putnam_2005_b5_partial_derivative i
    (putnam_2005_b5_partial_derivative i P).

Definition putnam_2005_b5_laplacian
    {n : nat}
    (P : putnam_2005_b5_polynomial n) :
    putnam_2005_b5_polynomial n :=
  List.flat_map
    (fun i => putnam_2005_b5_second_partial i P)
    (putnam_2005_b5_fin_enum n).

Definition putnam_2005_b5_square_variable
    {n : nat}
    (i : Fin.t n) :
    RbaseSymbolsImpl.R * (Fin.t n -> nat) :=
  (1,
   fun j => if Fin.eq_dec j i then 2%nat else 0%nat).

Definition putnam_2005_b5_sum_squares
    (n : nat) : putnam_2005_b5_polynomial n :=
  List.map putnam_2005_b5_square_variable
    (putnam_2005_b5_fin_enum n).

Theorem putnam_2005_b5
    (n : nat)
    (npos : (0 < n)%nat)
    (P : putnam_2005_b5_polynomial n)
    (hderiv :
      putnam_2005_b5_polynomial_eq
        (putnam_2005_b5_laplacian P)
        (putnam_2005_b5_zero n))
    (hsumsq :
      exists Q : putnam_2005_b5_polynomial n,
        putnam_2005_b5_polynomial_eq
          (putnam_2005_b5_polynomial_mul
            (putnam_2005_b5_sum_squares n) Q)
          P) :
  putnam_2005_b5_polynomial_eq P (putnam_2005_b5_zero n).
Proof.
Admitted.
