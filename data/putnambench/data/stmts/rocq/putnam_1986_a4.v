(* Statement-only formalization of PutnamBench artifact putnam_1986_a4:
   counting square matrices with entries in {-1, 0, 1} whose transversal
   sums are all equal, and giving the resulting closed formula. This file
   contains no proof. *)

From Stdlib Require Import ZArith QArith Qpower.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition putnam_1986_a4_entry {n : nat}
    (A : {ffun ('I_n * 'I_n) -> 'I_3}) (i j : 'I_n) : Z :=
  match nat_of_ord (A (i, j)) with
  | O => (-1)%Z
  | S O => 0%Z
  | _ => 1%Z
  end.

Fixpoint putnam_1986_a4_sum_indices {n : nat}
    (A : {ffun ('I_n * 'I_n) -> 'I_3})
    (p : {ffun 'I_n -> 'I_n}) (indices : seq 'I_n) : Z :=
  match indices with
  | [::] => 0%Z
  | i :: remaining =>
      (putnam_1986_a4_entry A i (p i) +
       putnam_1986_a4_sum_indices A p remaining)%Z
  end.

Definition putnam_1986_a4_transversal_sum {n : nat}
    (A : {ffun ('I_n * 'I_n) -> 'I_3})
    (p : {ffun 'I_n -> 'I_n}) : Z :=
  putnam_1986_a4_sum_indices A p (enum 'I_n).

Definition putnam_1986_a4_permutation {n : nat}
    (p : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i : 'I_n,
    [forall j : 'I_n, (p i == p j) ==> (i == j)]].

Definition putnam_1986_a4_admissible {n : nat}
    (A : {ffun ('I_n * 'I_n) -> 'I_3}) : bool :=
  [forall p : {ffun 'I_n -> 'I_n},
    [forall q : {ffun 'I_n -> 'I_n},
      (putnam_1986_a4_permutation p &&
       putnam_1986_a4_permutation q) ==>
      Z.eqb (putnam_1986_a4_transversal_sum A p)
            (putnam_1986_a4_transversal_sum A q)]].

Definition putnam_1986_a4_solution (n : nat) : Q :=
  (4 ^ Z.of_nat n + 2 * (3 ^ Z.of_nat n) -
   4 * (2 ^ Z.of_nat n) + 1)%Q.

Theorem putnam_1986_a4 (n : nat) (hn : (0 < n)%nat) :
  (inject_Z
     (Z.of_nat
       #|[pred A : {ffun ('I_n * 'I_n) -> 'I_3} |
           putnam_1986_a4_admissible A]|) ==
   putnam_1986_a4_solution n)%Q.
Admitted.
