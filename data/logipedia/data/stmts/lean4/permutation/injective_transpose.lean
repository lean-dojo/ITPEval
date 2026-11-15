-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.injective_transpose" (catalog title
-- "permutation.injective_transpose"): transposing any two natural numbers
-- defines an injective function on the natural numbers. This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem injective_transpose :
    forall i j : Nat, Function.Injective (transpose i j) := sorry

end permutation
