-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.transpose_i_j_j" (catalog title
-- "permutation.transpose_i_j_j"): transposing two natural numbers sends the
-- second transposed number to the first. This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem transpose_i_j_j :
    forall i j : Nat, transpose i j j = i := sorry

end permutation
