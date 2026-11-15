$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.transpose_i_j_j
  (logipedia__metamath__permutation.transpose_i_j_j), catalog title
  "permutation.transpose_i_j_j": transposing two natural numbers sends the
  second selected number to the first. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves both source natural-number domains. The nested conditional
  exactly unfolds permutation.transpose: it sends i to j, j to i, and every
  other input to itself. Here its input is j, so the displayed equality is
  precisely transpose i j j = i. SetMM's native equality represents the
  source equality predicate. The final declaration is Metamath's native
  unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d i j $.

  logipedia-permutation-transpose-i-j-j $a |-
    A. i e. NN0
      A. j e. NN0
        if ( j = i , j , if ( j = j , i , j ) ) = i
  $.
$}
