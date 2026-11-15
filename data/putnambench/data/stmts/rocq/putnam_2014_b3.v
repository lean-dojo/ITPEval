(* Statement-only formalization of PutnamBench corpus artifact putnam_2014_b3:
   a rational matrix with at least m+n distinct prime absolute entry values
   has rank at least two. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin QArith Qabs ZArith.Znumtheory.

Open Scope Q_scope.

Definition putnam_2014_b3_matrix (m n : nat) : Type :=
  Fin.t m -> Fin.t n -> Q.

Definition putnam_2014_b3_many_entry_primes
    {m n : nat} (A : putnam_2014_b3_matrix m n) : Prop :=
  exists ps : Fin.t (m + n) -> nat,
    (forall u v : Fin.t (m + n), ps u = ps v -> u = v) /\
    forall k : Fin.t (m + n),
      prime (Z.of_nat (ps k)) /\
      exists (i : Fin.t m) (j : Fin.t n),
        Qeq (Qabs (A i j)) (inject_Z (Z.of_nat (ps k))).

Theorem putnam_2014_b3
    (m n : nat)
    (A : putnam_2014_b3_matrix m n)
    (mnpos : (0 < m)%nat /\ (0 < n)%nat)
    (Aprime : putnam_2014_b3_many_entry_primes A) :
  exists (i1 i2 : Fin.t m) (j1 j2 : Fin.t n),
    i1 <> i2 /\
    j1 <> j2 /\
    ~ Qeq
        (A i1 j1 * A i2 j2 - A i1 j2 * A i2 j1)
        0.
Admitted.
