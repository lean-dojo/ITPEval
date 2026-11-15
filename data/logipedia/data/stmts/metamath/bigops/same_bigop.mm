$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.same_bigop, catalog title "bigops.same_bigop": two Boolean-filtered
  polymorphic big operations are equal when their predicates agree below the
  bound and their values agree at every selected index. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary set h models the source type B, NN0 models nat, and {0,1}
  models bool with 1 as true. Full SetMM function spaces preserve the source
  domains of predicates, sequences, and the curried binary operation.
  LogBigop h k represents the source bigop at bound k. The definitions of
  sameF_upto and sameF_p are expanded in the two antecedents. The explicit
  membership conjunct exposes the typing intrinsic to the source bigop
  declaration. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c LogBigop LogBigopType $.

log-bigop-syntax $a class ( LogBigop h k ) $.
log-bigop-type-syntax $a class ( LogBigopType h ) $.

log-bigop-type-definition $a |- ( LogBigopType h ) =
  (
    (
      (
        ( h ^m ( h ^m NN0 ) )
        ^m
        ( ( h ^m h ) ^m h )
      )
      ^m
      h
    )
    ^m
    ( { 0 , 1 } ^m NN0 )
  )
$.

${
  $d f g h i k o p q x $.

  logipedia-bigops-same-bigop $a |-
    A. h
      A. k e. NN0
        A. p e. ( { 0 , 1 } ^m NN0 )
          A. q e. ( { 0 , 1 } ^m NN0 )
            A. x e. h
              A. o e. ( ( h ^m h ) ^m h )
                A. f e. ( h ^m NN0 )
                  A. g e. ( h ^m NN0 )
                    (
                      ( LogBigop h k ) e. ( LogBigopType h )
                      /\
                      (
                        A. i e. NN0
                          (
                            i < k
                            ->
                            ( p ` i ) = ( q ` i )
                          )
                        ->
                        (
                          A. i e. NN0
                            (
                              i < k
                              ->
                              (
                                ( p ` i ) = 1
                                ->
                                ( f ` i ) = ( g ` i )
                              )
                            )
                          ->
                          (
                            ( ( ( ( ( LogBigop h k ) ` p ) ` x ) ` o ) ` f )
                            =
                            ( ( ( ( ( LogBigop h k ) ` q ) ` x ) ` o ) ` g )
                          )
                        )
                      )
                    )
  $.
$}
