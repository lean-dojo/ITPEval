(*
  Statement-only formalization of Thousand Theorems corpus artifact Q132469
  (thousand-theorems__rocq__Q132469), "Fermat's Last Theorem": for every
  natural exponent at least three, no three nonzero natural numbers satisfy
  a^n + b^n = c^n. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem FermatLastTheorem :
  forall n : nat,
    (3 <= n)%nat ->
    forall a b c : nat,
      a <> 0 ->
      b <> 0 ->
      c <> 0 ->
      Nat.pow a n + Nat.pow b n <> Nat.pow c n.
Admitted.
