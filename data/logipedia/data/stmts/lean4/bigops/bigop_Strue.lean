-- Statement-only formalization of Logipedia artifact "bigops.bigop_Strue":
-- a Boolean-filtered big operation adds the newly considered value at a successor
-- index when the predicate value there is true. This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem bigop_Strue
    (B : Type) (k : Nat) (p : Nat → Bool) (nil : B)
    (op : B → B → B) (f : Nat → B) (hpk : p k = true) :
    bigop B (Nat.succ k) p nil op f = op (f k) (bigop B k p nil op f) := sorry

end bigops
