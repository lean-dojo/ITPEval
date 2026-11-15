-- Statement-only formalization of Logipedia artifact "bigops.bigop_I_gen":
-- equality of a shifted bounded product with its lower-bound-filtered form.
-- This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem bigop_I_gen
    (a b : Nat) (p : Nat → Bool) (f : Nat → Nat) (hab : a ≤ b) :
    bigop Nat (b - a) (fun i ↦ p (i + a)) 1 Nat.mul (fun i ↦ f (i + a)) =
      bigop Nat b (fun i ↦ decide (a ≤ i) && p i) 1 Nat.mul f := sorry

end bigops
