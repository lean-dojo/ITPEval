(*
  Statement-only formalization of Logipedia corpus artifact
  primes.match_divides_prop (catalog title "primes.match_divides_prop"): the
  elimination principle for natural-number divisibility, using a quotient
  witness to establish an arbitrary proposition. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_match_divides_prop :
  forall n m : nat,
  forall return_type : Prop,
    (forall q : nat, m = n * q -> return_type) ->
    primes_divides n m ->
    return_type.
Admitted.
