(* Statement-only formalization of PutnamBench corpus artifact putnam_2014_a6:
   the largest size of two indexed families of real square matrices whose
   cross-products have a zero diagonal entry exactly off the matching index
   is n^n. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin Reals.

Open Scope R_scope.

Definition putnam_2014_a6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Fixpoint putnam_2014_a6_fin_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as m return (Fin.t m -> R) -> R with
  | O => fun _ => 0
  | S m =>
      fun f =>
        f Fin.F1 +
        putnam_2014_a6_fin_sum m (fun i => f (Fin.FS i))
  end.

Definition putnam_2014_a6_matrix_mul
    {n : nat}
    (A B : putnam_2014_a6_matrix n) :
    putnam_2014_a6_matrix n :=
  fun i j =>
    putnam_2014_a6_fin_sum n (fun p => A i p * B p j).

Definition putnam_2014_a6_solution (n : nat) : nat :=
  Nat.pow n n.

Theorem putnam_2014_a6
    (n : nat)
    (kex : nat -> Prop)
    (npos : (0 < n)%nat)
    (hkex :
      forall k : nat,
        (1 <= k)%nat ->
        (kex k <->
          exists M N : Fin.t k -> putnam_2014_a6_matrix n,
            forall i j : Fin.t k,
              ((exists p : Fin.t n,
                  putnam_2014_a6_matrix_mul (M i) (N j) p p = 0)
               <-> i <> j))) :
  ((1 <= putnam_2014_a6_solution n)%nat /\
    kex (putnam_2014_a6_solution n)) /\
  (forall k : nat,
    (1 <= k)%nat ->
    kex k ->
    (k <= putnam_2014_a6_solution n)%nat).
Admitted.
