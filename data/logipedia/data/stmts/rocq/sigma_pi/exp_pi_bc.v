(*
  Statement-only formalization of Logipedia corpus artifact
  sigma_pi.exp_pi_bc (catalog title "sigma_pi.exp_pi_bc"): multiplying a
  shifted finite product by a natural power distributes one copy of the base
  into every factor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Fixpoint sigma_pi_bigop {H : Type}
    (n : nat) (p : nat -> bool) (nil : H)
    (op : H -> H -> H) (f : nat -> H) : H :=
  match n with
  | O => nil
  | S k =>
      if p k
      then op (f k) (sigma_pi_bigop k p nil op f)
      else sigma_pi_bigop k p nil op f
  end.

Fixpoint sigma_pi_exp (a n : nat) : nat :=
  match n with
  | O => 1
  | S k => Nat.mul (sigma_pi_exp a k) a
  end.

Theorem exp_pi_bc :
  forall (a b c : nat) (f : nat -> nat),
    Nat.mul
      (sigma_pi_exp a (Nat.sub c b))
      (sigma_pi_bigop
        (Nat.sub c b)
        (fun _ => true)
        1
        Nat.mul
        (fun i => f (Nat.add i b))) =
    sigma_pi_bigop
      (Nat.sub c b)
      (fun _ => true)
      1
      Nat.mul
      (fun i => Nat.mul a (f (Nat.add i b))).
Admitted.
