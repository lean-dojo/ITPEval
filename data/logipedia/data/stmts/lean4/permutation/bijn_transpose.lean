-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.bijn_transpose" (catalog title "permutation.bijn_transpose"):
-- transposing two natural numbers in an initial segment is surjective on that
-- initial segment when both transposed numbers lie in it.
-- This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

def bijn (f : Nat -> Nat) (n : Nat) : Prop :=
  forall m : Nat, m <= n -> Exists fun p : Nat => And (p <= n) (f p = m)

theorem bijn_transpose :
    forall n i j : Nat, i <= n -> j <= n -> bijn (transpose i j) n := sorry

end permutation
