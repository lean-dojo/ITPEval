-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.transpose_i_j_i" (catalog title
-- "permutation.transpose_i_j_i"): transposing two natural numbers sends the
-- first transposed number to the second. This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem transpose_i_j_i :
    forall i j : Nat, transpose i j i = j := sorry

end permutation
