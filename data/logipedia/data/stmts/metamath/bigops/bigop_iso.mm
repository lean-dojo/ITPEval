$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_iso: an isomorphism between Boolean-selected initial segments
  that preserves natural-valued entries yields equality of their filtered
  finite products. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain and {0,1} is the Boolean carrier,
  with true represented by 1. The source definition of iso is unfolded:
  h and k are total functions on NN0 that map selected indices in both
  directions, are inverse on those indices, and h preserves the selected
  function values. Each source bigop with base 1 and natural multiplication
  is represented by the product over the selected part of the corresponding
  half-open initial interval. The final declaration is an unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d a b f g h i j k p q $.

  logipedia-bigops-bigop-iso $a |-
    A. a e. NN0
      A. b e. NN0
        A. p e. ( { 0 , 1 } ^m NN0 )
          A. q e. ( { 0 , 1 } ^m NN0 )
            A. f e. ( NN0 ^m NN0 )
              A. g e. ( NN0 ^m NN0 )
                (
                  (
                    E. h e. ( NN0 ^m NN0 )
                      E. k e. ( NN0 ^m NN0 )
                        (
                          (
                            A. i e. NN0
                              (
                                i < a
                                ->
                                (
                                  ( p ` i ) = 1
                                  ->
                                  ( f ` i ) = ( g ` ( h ` i ) )
                                )
                              )
                            /\
                            A. i e. NN0
                              (
                                i < a
                                ->
                                (
                                  ( p ` i ) = 1
                                  ->
                                  (
                                    (
                                      ( h ` i ) < b
                                      /\
                                      ( q ` ( h ` i ) ) = 1
                                    )
                                    /\
                                    ( k ` ( h ` i ) ) = i
                                  )
                                )
                              )
                          )
                          /\
                          A. j e. NN0
                            (
                              j < b
                              ->
                              (
                                ( q ` j ) = 1
                                ->
                                (
                                  (
                                    ( k ` j ) < a
                                    /\
                                    ( p ` ( k ` j ) ) = 1
                                  )
                                  /\
                                  ( h ` ( k ` j ) ) = j
                                )
                              )
                            )
                        )
                  )
                  ->
                  (
                    prod_ i e.
                      {
                        i e. ( 0 ..^ a )
                        |
                        ( p ` i ) = 1
                      }
                      ( f ` i )
                  )
                  =
                  (
                    prod_ j e.
                      {
                        j e. ( 0 ..^ b )
                        |
                        ( q ` j ) = 1
                      }
                      ( g ` j )
                  )
                )
  $.
$}
