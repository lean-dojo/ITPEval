-- Statement-only formalization of Logipedia artifact "bigops.bigop_Sfalse":
-- a Boolean-filtered big operation is unchanged at a successor index when the
-- newly considered predicate value is false. This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem bigop_Sfalse
    (B : Type) (k : Nat) (p : Nat → Bool) (nil : B)
    (op : B → B → B) (f : Nat → B) (hpk : p k = false) :
    bigop B (Nat.succ k) p nil op f = bigop B k p nil op f := sorry

end bigops
