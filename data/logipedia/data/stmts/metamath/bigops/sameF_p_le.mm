$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sameF_p_le, catalog title "bigops.sameF_p_le": pointwise agreement
  of two natural-indexed functions at predicate-selected indices below a
  bound is preserved when the bound is decreased. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary set a models the source type A, { 0 , 1 } models bool with
  1 as true, and NN0 models nat. The source definition sameF_p A k p f g is
  expanded as agreement of f and g at every natural i below k for which
  p i is true. The antecedent uses bound m and the conclusion uses bound n,
  under the source assumption n <= m. This is an unproved $a statement
  encoding; the database contains no $p proof declaration.
$)

${
  $d a f g i m n p $.

  logipedia-bigops-samef-p-le $a |-
    A. a
      A. p e. ( { 0 , 1 } ^m NN0 )
        A. f e. ( a ^m NN0 )
          A. g e. ( a ^m NN0 )
            A. n e. NN0
              A. m e. NN0
                (
                  n <_ m
                  ->
                  (
                    A. i e. NN0
                      (
                        i < m
                        ->
                        (
                          ( p ` i ) = 1
                          ->
                          ( f ` i ) = ( g ` i )
                        )
                      )
                    ->
                    A. i e. NN0
                      (
                        i < n
                        ->
                        (
                          ( p ` i ) = 1
                          ->
                          ( f ` i ) = ( g ` i )
                        )
                      )
                  )
                )
  $.
$}
