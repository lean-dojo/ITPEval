-- Statement-only formalization of Logipedia corpus artifact "bigops.bigop_false"
-- (catalog title "bigops.bigop_false"): a Boolean-filtered polymorphic big operation
-- with a constantly false selector returns its supplied neutral value at every
-- natural bound. This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem bigop_false
    (B : Type) (n : Nat) (nil : B) (op : B → B → B) (f : Nat → B) :
    bigop B n (fun _ ↦ false) nil op f = nil := sorry

end bigops
