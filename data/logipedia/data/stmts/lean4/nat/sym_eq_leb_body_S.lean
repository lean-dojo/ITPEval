-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_leb_body_S" (catalog title "nat.sym_eq_leb_body_S"): directed
-- Leibniz equality relates the recursive Boolean less-than-or-equal step at a
-- successor to the fixed less-than-or-equal test body at that successor. This
-- file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def matchNatType (R : Type) (caseO : R) (caseS : Nat → R) : Nat → R
  | 0 => caseO
  | Nat.succ n => caseS n

def leb : Nat → Nat → Bool
  | 0, _m => true
  | Nat.succ _n, 0 => false
  | Nat.succ n, Nat.succ m => leb n m

def lebBody : Nat → Nat → Bool
  | 0, _m => true
  | Nat.succ n, m => matchNatType Bool false (fun q ↦ leb n q) m

theorem sym_eq_leb_body_S :
    ∀ n : Nat,
      Leibniz (Nat → Bool)
        (fun m ↦ matchNatType Bool false (fun q ↦ leb n q) m)
        (lebBody (Nat.succ n)) := sorry

end nat
