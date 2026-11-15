$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_i_j_i
  (logipedia__metamath__permutation.transpose_i_j_i), catalog title
  "permutation.transpose_i_j_i": transposing two natural numbers sends the
  first selected number to the second. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves both source natural-number domains. The nested conditional
  exactly unfolds permutation.transpose: it sends i to j, j to i, and every
  other input to itself. Here its input is i, so the displayed equality is
  precisely transpose i j i = j. SetMM's native equality represents the
  source equality predicate. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d i j $.

  logipedia-permutation-transpose-i-j-i $a |-
    A. i e. NN0
      A. j e. NN0
        if ( i = i , j , if ( i = j , i , i ) ) = j
  $.
$}
