(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.eq_fact_pi_p (catalog title "fermat.eq_fact_pi_p"): for every
  natural number, its factorial equals the filtered finite product of the
  successors from one through that number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Fixpoint fermat_bigop {H : Type}
    (n : nat) (p : nat -> bool) (nil : H)
    (op : H -> H -> H) (f : nat -> H) : H :=
  match n with
  | O => nil
  | S k =>
      if p k
      then op (f k) (fermat_bigop k p nil op f)
      else fermat_bigop k p nil op f
  end.

Fixpoint fermat_fact (n : nat) : nat :=
  match n with
  | O => S O
  | S k => Nat.mul (fermat_fact k) (S k)
  end.

Theorem eq_fact_pi_p :
  forall n : nat,
    fermat_fact n =
    fermat_bigop
      (Nat.sub (S n) (S O))
      (fun _ => true)
      (S O)
      Nat.mul
      (fun i => Nat.add i (S O)).
Admitted.
