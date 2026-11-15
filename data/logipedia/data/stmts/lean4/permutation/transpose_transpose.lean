-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.transpose_transpose" (catalog title
-- "permutation.transpose_transpose"): transposing the same two natural
-- numbers twice returns the original natural number. This file contains no proof.

namespace permutation

def transpose (i j n : Nat) : Nat :=
  if n = i then j else if n = j then i else n

theorem transpose_transpose :
    forall i j n : Nat, transpose i j (transpose i j n) = n := sorry

end permutation
