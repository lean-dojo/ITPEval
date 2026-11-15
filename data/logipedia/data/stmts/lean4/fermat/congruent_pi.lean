-- Statement-only formalization of Logipedia corpus artifact
-- "fermat.congruent_pi" (catalog title "fermat.congruent_pi"): for every
-- natural-valued function, the product of its first n values is congruent
-- modulo a positive natural modulus to the product of their remainders.
-- This file contains no proof.

namespace fermat

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

def congruent (left right modulus : Nat) : Prop :=
  left % modulus = right % modulus

theorem congruent_pi :
    ∀ (f : Nat → Nat) (n p : Nat), 0 < p →
      congruent
        (bigop Nat n (fun _ => true) 1 Nat.mul f)
        (bigop Nat n (fun _ => true) 1 Nat.mul (fun i => f i % p))
        p := sorry

end fermat
