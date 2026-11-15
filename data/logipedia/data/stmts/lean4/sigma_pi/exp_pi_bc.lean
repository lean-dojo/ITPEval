-- Statement-only formalization of Logipedia corpus artifact "sigma_pi.exp_pi_bc"
-- (catalog title "sigma_pi.exp_pi_bc"): distributing a constant natural factor
-- across a shifted finite product. This file contains no proof.

namespace sigma_pi

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem exp_pi_bc (a b c : Nat) (f : Nat → Nat) :
    a ^ (c - b) *
        bigop Nat (c - b) (fun _ => true) 1 Nat.mul (fun i => f (i + b)) =
      bigop Nat (c - b) (fun _ => true) 1 Nat.mul (fun i => a * f (i + b)) := sorry

end sigma_pi
