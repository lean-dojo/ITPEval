(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_mod_to_divides (catalog title "gcd.divides_mod_to_divides"):
  for natural numbers p, m, and positive n, if p divides the source remainder
  of m modulo n and p divides n, then p divides m. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint gcd_source_mod_aux (fuel value modulus_pred : nat) {struct fuel} : nat :=
  match fuel with
  | O => value
  | S remaining =>
      if Nat.leb value modulus_pred
      then value
      else gcd_source_mod_aux remaining (value - S modulus_pred) modulus_pred
  end.

Definition gcd_source_mod (value modulus : nat) : nat :=
  match modulus with
  | O => value
  | S modulus_pred => gcd_source_mod_aux value value modulus_pred
  end.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem divides_mod_to_divides :
  forall p m n : nat,
    O < n ->
    gcd_divides p (gcd_source_mod m n) ->
    gcd_divides p n ->
    gcd_divides p m.
Admitted.
