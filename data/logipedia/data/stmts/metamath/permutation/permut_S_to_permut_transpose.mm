$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.permut_S_to_permut_transpose
  (logipedia__metamath__permutation.permut_S_to_permut_transpose), catalog
  title "permutation.permut_S_to_permut_transpose": a permutation of the
  natural-number initial segment through successor m induces a permutation
  through m after transposing its value at successor m with successor m.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total
  endofunction domains. Both occurrences of permutation.permut are unfolded
  as closure on an inclusive initial segment together with injectivity on
  that segment. The nested conditional exactly unfolds
  permutation.transpose, and m + 1 represents the source successor S m.
  Restricted quantifiers, implications, conjunctions, and SetMM equality
  preserve the source binder order, assumptions, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

${
  $d f i j m $.

  logipedia-permutation-permut-s-to-permut-transpose $a |-
    A. f e. ( NN0 ^m NN0 )
      A. m e. NN0
        (
          (
            (
              A. i e. NN0
                (
                  i <_ ( m + 1 )
                  ->
                  ( f ` i ) <_ ( m + 1 )
                )
            )
            /\
            A. i e. NN0
              A. j e. NN0
                (
                  i <_ ( m + 1 )
                  ->
                  (
                    j <_ ( m + 1 )
                    ->
                    (
                      ( f ` i ) = ( f ` j )
                      ->
                      i = j
                    )
                  )
                )
          )
          ->
          (
            (
              A. i e. NN0
                (
                  i <_ m
                  ->
                  if (
                    ( f ` i ) = ( f ` ( m + 1 ) ) ,
                    ( m + 1 ) ,
                    if (
                      ( f ` i ) = ( m + 1 ) ,
                      ( f ` ( m + 1 ) ) ,
                      ( f ` i )
                    )
                  ) <_ m
                )
            )
            /\
            A. i e. NN0
              A. j e. NN0
                (
                  i <_ m
                  ->
                  (
                    j <_ m
                    ->
                    (
                      if (
                        ( f ` i ) = ( f ` ( m + 1 ) ) ,
                        ( m + 1 ) ,
                        if (
                          ( f ` i ) = ( m + 1 ) ,
                          ( f ` ( m + 1 ) ) ,
                          ( f ` i )
                        )
                      )
                      =
                      if (
                        ( f ` j ) = ( f ` ( m + 1 ) ) ,
                        ( m + 1 ) ,
                        if (
                          ( f ` j ) = ( m + 1 ) ,
                          ( f ` ( m + 1 ) ) ,
                          ( f ` j )
                        )
                      )
                      ->
                      i = j
                    )
                  )
                )
          )
        )
  $.
$}
