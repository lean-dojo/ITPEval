$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sameF_upto_le, catalog title "bigops.sameF_upto_le": pointwise
  agreement of two natural-indexed functions below a bound is preserved when
  the bound is decreased. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary set a models the source type A, and NN0 models nat. The
  source definition sameF_upto A k f g is expanded as agreement of f and g
  at every natural i below k. The antecedent uses bound m and the conclusion
  uses bound n, under the source assumption n <= m. This is an unproved $a
  statement encoding; the database contains no $p proof declaration.
$)

${
  $d a f g i m n $.

  logipedia-bigops-samef-upto-le $a |-
    A. a
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
                      ( f ` i ) = ( g ` i )
                    )
                  ->
                  A. i e. NN0
                    (
                      i < n
                      ->
                      ( f ` i ) = ( g ` i )
                    )
                )
              )
  $.
$}
