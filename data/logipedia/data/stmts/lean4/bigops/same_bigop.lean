-- Statement-only formalization of Logipedia corpus artifact "bigops.same_bigop"
-- (catalog title "bigops.same_bigop"): Boolean-filtered big operations agree
-- below a bound when their predicates and selected function values agree.
-- This file contains no proof.

namespace bigops

def sameF_upto (A : Type) (k : Nat) (f g : Nat → A) : Prop :=
  ∀ i : Nat, i < k → f i = g i

def sameF_p (A : Type) (k : Nat) (p : Nat → Bool) (f g : Nat → A) : Prop :=
  ∀ i : Nat, i < k → p i = true → f i = g i

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem same_bigop
    (B : Type) (k : Nat) (p1 p2 : Nat → Bool) (nil : B)
    (op : B → B → B) (f g : Nat → B)
    (hp : sameF_upto Bool k p1 p2)
    (hfg : sameF_p B k p1 f g) :
    bigop B k p1 nil op f = bigop B k p2 nil op g := sorry

end bigops
