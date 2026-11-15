(*
  Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_l
  (catalog title "sigma_pi.exp_pi_l"): multiplying a finite product of
  natural values by a natural base raised to the number of factors equals
  the product obtained by multiplying every factor by that base. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool.

Fixpoint sigma_pi_exp (a n : nat) : nat :=
  match n with
  | O => S O
  | S k => Nat.mul (sigma_pi_exp a k) a
  end.

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

Theorem sigma_pi_exp_pi_l :
  forall (n a : nat) (f : nat -> nat),
    Nat.mul
      (sigma_pi_exp a n)
      (sigma_pi_bigop n (fun _ => true) (S O) Nat.mul f) =
    sigma_pi_bigop
      n
      (fun _ => true)
      (S O)
      Nat.mul
      (fun i => Nat.mul a (f i)).
Admitted.
