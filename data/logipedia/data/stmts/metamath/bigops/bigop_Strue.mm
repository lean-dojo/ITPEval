$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_Strue: a Boolean-filtered polymorphic big operation at a
  successor bound applies the binary operation to the newly considered value
  and the preceding big operation when the predicate is true at that index.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary, NN0 is the source natural-number domain,
  and {0,1} is the Boolean carrier with true represented by 1. Full SetMM
  function spaces encode the source predicate, binary operation, and sequence
  domains. LogBigop h k represents the source bigop at bound k. The explicit
  membership conjuncts expose typing intrinsic to the source declaration.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
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
  $d f h k o p x $.

  logipedia-bigops-bigop-strue $a |-
    A. h
      A. k e. NN0
        A. p e. ( { 0 , 1 } ^m NN0 )
          A. x e. h
            A. o e. ( ( h ^m h ) ^m h )
              A. f e. ( h ^m NN0 )
                (
                  (
                    ( LogBigop h ( k + 1 ) ) e. ( LogBigopType h )
                    /\
                    ( LogBigop h k ) e. ( LogBigopType h )
                  )
                  /\
                  (
                    ( p ` k ) = 1
                    ->
                    (
                      ( ( ( ( ( LogBigop h ( k + 1 ) ) ` p ) ` x ) ` o ) ` f )
                      =
                      (
                        ( o ` ( f ` k ) )
                        `
                        ( ( ( ( ( LogBigop h k ) ` p ) ` x ) ` o ) ` f )
                      )
                    )
                  )
                )
  $.
$}
