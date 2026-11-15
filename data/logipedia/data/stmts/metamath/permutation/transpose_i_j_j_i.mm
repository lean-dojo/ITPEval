$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_i_j_j_i
  (logipedia__metamath__permutation.transpose_i_j_j_i), catalog title
  "permutation.transpose_i_j_j_i": swapping two natural numbers is unchanged
  when the two selected numbers are supplied in the opposite order. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves all three source natural-number domains. Each nested
  conditional exactly unfolds permutation.transpose: transpose i j n sends i
  to j, sends j to i, and otherwise returns n. The right side unfolds
  transpose j i n in the same way, so the displayed equality is precisely the
  source conclusion transpose i j n = transpose j i n. SetMM's native
  equality preserves the source equality predicate. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d i j n $.

  logipedia-permutation-transpose-i-j-j-i $a |-
    A. i e. NN0
      A. j e. NN0
        A. n e. NN0
          if ( n = i , j , if ( n = j , i , n ) )
          =
          if ( n = j , i , if ( n = i , j , n ) )
  $.
$}
