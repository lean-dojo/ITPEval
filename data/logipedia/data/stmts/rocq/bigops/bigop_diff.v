(* Statement-only formalization of Logipedia corpus artifact bigops.bigop_diff:
   removing one selected factor from a finite filtered product and multiplying
   it back preserves the product. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Fixpoint bigop {H : Type}
    (n : nat) (p : nat -> bool) (nil : H)
    (op : H -> H -> H) (f : nat -> H) : H :=
  match n with
  | O => nil
  | S k =>
      if p k
      then op (f k) (bigop k p nil op f)
      else bigop k p nil op f
  end.

Theorem bigops_bigop_diff :
  forall (p : nat -> bool) (f : nat -> nat) (i n : nat),
    i < n ->
    p i = true ->
    bigop n p 1 Nat.mul f =
    Nat.mul (f i)
      (bigop n
        (fun x => andb (negb (Nat.eqb i x)) (p x))
        1 Nat.mul f).
Admitted.
