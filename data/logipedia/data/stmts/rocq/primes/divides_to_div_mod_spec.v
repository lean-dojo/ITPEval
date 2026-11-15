(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_div_mod_spec (catalog title
  "primes.divides_to_div_mod_spec"): a positive natural number dividing a
  natural number gives the source quotient with remainder zero in the
  division specification. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint div_mod_source_div_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => O
  | S q =>
      if Nat.leb n m
      then O
      else S (div_mod_source_div_aux q (n - S m) m)
  end.

Definition div_mod_source_div (n m : nat) : nat :=
  match m with
  | O => S n
  | S p => div_mod_source_div_aux n n p
  end.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Inductive div_mod_spec (n m q r : nat) : Prop :=
| div_mod_spec_intro :
    r < m ->
    n = q * m + r ->
    div_mod_spec n m q r.

Theorem logipedia_primes_divides_to_div_mod_spec :
  forall n m : nat,
    O < n ->
    primes_divides n m ->
    div_mod_spec m n (div_mod_source_div m n) O.
Admitted.
