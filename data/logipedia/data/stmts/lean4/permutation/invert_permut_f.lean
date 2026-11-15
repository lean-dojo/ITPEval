-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.invert_permut_f" (catalog title
-- "permutation.invert_permut_f"): a bounded injective natural-number function
-- is recovered on its initial segment by the recursively constructed inverse.
-- This file contains no proof.

namespace permutation

def injn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall i j : Nat, i <= n -> j <= n -> f i = f j -> i = j

def invertPermut : Nat -> (Nat -> Nat) -> Nat -> Nat
  | 0, _, _ => 0
  | Nat.succ n, f, m =>
      if m = f (Nat.succ n) then Nat.succ n else invertPermut n f m

theorem invert_permut_f :
    forall (f : Nat -> Nat) (n m : Nat),
      m <= n -> injn f n -> invertPermut n f (f m) = m := sorry

end permutation
