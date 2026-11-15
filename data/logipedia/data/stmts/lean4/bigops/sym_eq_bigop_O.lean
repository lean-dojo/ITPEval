-- Statement-only formalization of Logipedia corpus artifact "bigops.sym_eq_bigop_O"
-- (catalog title "bigops.sym_eq_bigop_O"): directed Leibniz equality at index zero
-- between the fixed Boolean-filtered big-operation families. This file contains no proof.

namespace bigops

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def bigop (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

def bigop_body (H : Type) :
    Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem sym_eq_bigop_O :
    ∀ H : Type,
      Leibniz ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigop_body H 0) (bigop H 0) := sorry

end bigops
