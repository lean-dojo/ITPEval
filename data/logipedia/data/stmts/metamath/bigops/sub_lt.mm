$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sub_lt, catalog title "bigops.sub_lt": under n <= m, identity maps
  satisfy the selected-index relation sub_hk from bound n to bound m for an
  arbitrary Boolean predicate and natural-valued function. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and { 0 , 1 } is the Boolean
  carrier with true represented by 1. Full SetMM function spaces preserve the
  arbitrary Boolean predicate p and natural-number-valued function e. The
  conclusion explicitly unfolds sub_hk with both index maps specialized to
  identity; the duplicated predicate and function arguments are thereby
  preserved, including the source definition's non-use of e. The declaration
  is an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d e i m n p $.

  logipedia-bigops-sub-lt $a |-
    A. e e. ( NN0 ^m NN0 )
      A. p e. ( { 0 , 1 } ^m NN0 )
        A. n e. NN0
          A. m e. NN0
            (
              n <_ m
              ->
              A. i e. NN0
                (
                  i < n
                  ->
                  (
                    ( p ` i ) = 1
                    ->
                    (
                      (
                        i < m
                        /\
                        ( p ` i ) = 1
                      )
                      /\
                      i = i
                    )
                  )
                )
            )
  $.
$}
