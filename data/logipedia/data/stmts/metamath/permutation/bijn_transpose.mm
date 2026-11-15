$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.bijn_transpose
  (logipedia__metamath__permutation.bijn_transpose), catalog title
  "permutation.bijn_transpose": swapping two natural numbers bounded by n is
  surjective on the natural-number initial segment through n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves every source natural-number domain. The nested conditional
  exactly unfolds permutation.transpose: it sends i to j, j to i, and every
  other input to itself. The conclusion directly unfolds permutation.bijn:
  every m at most n has a preimage p at most n. Restricted quantifiers,
  nested implications, and SetMM's native equality preserve the source
  binder order, assumptions, and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

${
  $d i j m n p $.

  logipedia-permutation-bijn-transpose $a |-
    A. n e. NN0
      A. i e. NN0
        A. j e. NN0
          (
            i <_ n
            ->
            (
              j <_ n
              ->
              A. m e. NN0
                (
                  m <_ n
                  ->
                  E. p e. NN0
                    (
                      p <_ n
                      /\
                      if ( p = i , j , if ( p = j , i , p ) ) = m
                    )
                )
            )
          )
  $.
$}
