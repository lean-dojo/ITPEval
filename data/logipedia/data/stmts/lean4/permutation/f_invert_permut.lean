-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.f_invert_permut" (catalog title
-- "permutation.f_invert_permut"): the recursively constructed inverse of a
-- permutation of a natural-number initial segment is a right inverse there.
-- This file contains no proof.

namespace permutation

def injn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall i j : Nat, i <= n -> j <= n -> f i = f j -> i = j

def permut (f : Nat -> Nat) (n : Nat) : Prop :=
  (forall i : Nat, i <= n -> f i <= n) /\ injn f n

def invertPermut : Nat -> (Nat -> Nat) -> Nat -> Nat
  | 0, _, _ => 0
  | Nat.succ n, f, m =>
      if m = f (Nat.succ n) then Nat.succ n else invertPermut n f m

theorem f_invert_permut :
    forall (f : Nat -> Nat) (n m : Nat),
      m <= n -> permut f n -> f (invertPermut n f m) = m := sorry

end permutation
