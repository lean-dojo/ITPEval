-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.transpose_i_j_j_i" (catalog title
-- "permutation.transpose_i_j_j_i"): transposing two natural numbers is
-- unchanged when the two transposed numbers are exchanged.
-- This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem transpose_i_j_j_i :
    forall i j n : Nat, transpose i j n = transpose j i n := sorry

end permutation
