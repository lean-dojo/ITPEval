$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.injective_transpose
  (logipedia__metamath__permutation.injective_transpose), catalog title
  "permutation.injective_transpose": transposing any two natural numbers
  defines an injective natural-number endofunction. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves every source natural-number domain. Each nested conditional
  exactly unfolds permutation.transpose: it sends i to j, j to i, and every
  other input to itself. Expanding relations.injective gives the restricted
  universal quantifiers over x and y and the implication from equality of
  their transposed images to x = y. SetMM's native equality preserves the
  source equality predicate. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d i j x y $.

  logipedia-permutation-injective-transpose $a |-
    A. i e. NN0
      A. j e. NN0
        A. x e. NN0
          A. y e. NN0
            (
              (
                if ( x = i , j , if ( x = j , i , x ) )
                =
                if ( y = i , j , if ( y = j , i , y ) )
              )
              ->
              x = y
            )
  $.
$}
