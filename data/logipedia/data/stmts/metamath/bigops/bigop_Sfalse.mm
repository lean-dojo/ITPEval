$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_Sfalse: a Boolean-filtered polymorphic big operation is
  unchanged at a successor bound when the predicate is false at the newly
  considered index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary, NN0 is the source natural-number domain,
  and {0,1} is the Boolean carrier with false represented by 0. Full SetMM
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

  logipedia-bigops-bigop-sfalse $a |-
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
                    ( p ` k ) = 0
                    ->
                    (
                      ( ( ( ( ( LogBigop h ( k + 1 ) ) ` p ) ` x ) ` o ) ` f )
                      =
                      ( ( ( ( ( LogBigop h k ) ` p ) ` x ) ` o ) ` f )
                    )
                  )
                )
  $.
$}
