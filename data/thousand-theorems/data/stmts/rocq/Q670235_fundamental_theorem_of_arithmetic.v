(*
  Statement-only formalization of Thousand Theorems corpus artifact Q670235
  (thousand-theorems__rocq__Q670235), "Fundamental theorem of arithmetic":
  every list of natural primes with product n is a permutation of the
  canonical increasing prime-factor list of n. This file contains no proof.
*)

From mathcomp Require Import ssreflect ssrbool ssrnat seq div bigop prime.

Definition q670235_prime_factors_list (n : nat) : seq nat :=
  flatten [seq nseq (snd pe) (fst pe) | pe <- prime_decomp n].

Definition q670235_list_product (l : seq nat) : nat :=
  foldr muln 1 l.

Theorem primeFactorsList_unique :
  forall (n : nat) (l : seq nat),
    q670235_list_product l = n ->
    (forall p : nat, p \in l -> prime p) ->
    perm_eq l (q670235_prime_factors_list n).
Admitted.
