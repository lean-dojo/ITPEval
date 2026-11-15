-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_eqb_body_S" (catalog title "nat.sym_eq_eqb_body_S"): directed
-- Leibniz equality relates the recursive Boolean equality-test step at a
-- successor to the fixed equality-test body at that successor. This file
-- contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def matchNatType (R : Type) (caseO : R) (caseS : Nat → R) : Nat → R
  | 0 => caseO
  | Nat.succ n => caseS n

def eqb : Nat → Nat → Bool
  | 0, m => matchNatType Bool true (fun _q ↦ false) m
  | Nat.succ n, m => matchNatType Bool false (fun q ↦ eqb n q) m

def eqbBody : Nat → Nat → Bool
  | 0, m => matchNatType Bool true (fun _q ↦ false) m
  | Nat.succ n, m => matchNatType Bool false (fun q ↦ eqb n q) m

theorem sym_eq_eqb_body_S :
    ∀ n : Nat,
      Leibniz (Nat → Bool)
        (fun m ↦ matchNatType Bool false (fun q ↦ eqb n q) m)
        (eqbBody (Nat.succ n)) := sorry

end nat
