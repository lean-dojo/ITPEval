-- Statement-only formalization of Logipedia corpus artifact
-- "fermat.eq_fact_pi_p" (catalog title "fermat.eq_fact_pi_p"): every natural
-- factorial equals the product of the first n positive natural numbers,
-- encoded by the source's filtered finite big operation. This file contains no proof.

namespace fermat

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem eq_fact_pi_p :
    ∀ n : Nat,
      factorial n =
        bigop Nat (Nat.succ n - Nat.succ 0) (fun _ => true) (Nat.succ 0)
          Nat.mul (fun i => i + Nat.succ 0) := sorry

end fermat
