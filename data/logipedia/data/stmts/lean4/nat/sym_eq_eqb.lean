-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_eqb"
-- (catalog title "nat.sym_eq_eqb"): at every natural argument, the naturally
-- filtered body of the recursive Boolean equality test is Leibniz-equal to
-- the corresponding partially applied equality test. This file contains no proof.

namespace nat

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def filterNatType (R : Type) (f : Nat → R) (n : Nat) : R :=
  f n

def eqb : Nat → Nat → Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ n, Nat.succ m => eqb n m

def eqbBody : Nat → Nat → Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ n, Nat.succ m => eqb n m

theorem sym_eq_eqb :
    ∀ n : Nat,
      Leibniz (Nat → Bool)
        (filterNatType (Nat → Bool) eqbBody n)
        (eqb n) := sorry

end nat
