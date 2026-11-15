-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.injn_Sn_n" (catalog title "permutation.injn_Sn_n"):
-- injectivity of a natural-number function on the initial segment through
-- n + 1 implies injectivity on the initial segment through n.
-- This file contains no proof.

namespace permutation

def injn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall i j : Nat, i <= n -> j <= n -> f i = f j -> i = j

theorem injn_Sn_n (f : Nat -> Nat) (n : Nat) :
    injn f (Nat.succ n) -> injn f n := sorry

end permutation
