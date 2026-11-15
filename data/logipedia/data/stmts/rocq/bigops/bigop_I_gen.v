(* Statement-only formalization of Logipedia corpus artifact
   bigops.bigop_I_gen: equality between a shifted finite product and the
   corresponding lower-bound-filtered finite product. This file contains
   no proof. *)

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

Theorem bigops_bigop_I_gen :
  forall (a b : nat) (p : nat -> bool) (f : nat -> nat),
    Nat.le a b ->
    bigop (Nat.sub b a)
      (fun i => p (Nat.add i a))
      1 Nat.mul
      (fun i => f (Nat.add i a)) =
    bigop b
      (fun i => andb (Nat.leb a i) (p i))
      1 Nat.mul
      (fun i => f i).
Admitted.
