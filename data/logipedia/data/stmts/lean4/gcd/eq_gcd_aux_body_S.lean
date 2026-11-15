-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.eq_gcd_aux_body_S" (catalog title "gcd.eq_gcd_aux_body_S"): at every
-- successor recursion index, the concrete auxiliary greatest-common-divisor
-- body is Leibniz-equal to its divisibility-controlled recursive step.
-- This file contains no proof.

namespace gcd

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def natEqb : Nat → Nat → Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ m, Nat.succ n => natEqb m n

def modAux : Nat → Nat → Nat → Nat
  | 0, m, _ => m
  | Nat.succ p, m, n =>
      if m ≤ n then m else modAux p (m - Nat.succ n) n

def naturalMod (m n : Nat) : Nat :=
  match n with
  | 0 => m
  | Nat.succ p => modAux m m p

def dividesb (n m : Nat) : Bool :=
  natEqb (naturalMod m n) 0

def gcdAux : Nat → Nat → Nat → Nat
  | 0, m, _ => m
  | Nat.succ p, m, n =>
      if dividesb n m then n else gcdAux p n (naturalMod m n)

def gcdAuxBody : Nat → Nat → Nat → Nat
  | 0, m, _ => m
  | Nat.succ p, m, n =>
      if dividesb n m then n else gcdAux p n (naturalMod m n)

theorem eq_gcd_aux_body_S :
    ∀ p : Nat,
      Leibniz (Nat → Nat → Nat) (gcdAuxBody (Nat.succ p))
        (fun m n ↦
          if dividesb n m then n else gcdAux p n (naturalMod m n)) := sorry

end gcd
