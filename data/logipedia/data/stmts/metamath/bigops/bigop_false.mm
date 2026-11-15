$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.bigop_false: a Boolean-filtered polymorphic big operation whose
  predicate is constantly false returns its base value at every natural
  bound. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary, NN0 is the source natural-number domain,
  and {0,1} is the Boolean carrier with false represented by 0. Full SetMM
  function spaces encode the source binary operation and sequence domains.
  The maps-to term ( i e. NN0 |-> 0 ) is the constant-false predicate, and
  LogBigop h k represents the source bigop at bound k. The explicit
  membership conjunct exposes typing intrinsic to the source declaration.
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
  $d f h i k o x $.

  logipedia-bigops-bigop-false $a |-
    A. h
      A. k e. NN0
        A. x e. h
          A. o e. ( ( h ^m h ) ^m h )
            A. f e. ( h ^m NN0 )
              (
                ( LogBigop h k ) e. ( LogBigopType h )
                /\
                (
                  (
                    (
                      (
                        ( LogBigop h k )
                        ` ( i e. NN0 |-> 0 )
                      )
                      ` x
                    )
                    ` o
                  )
                  ` f
                )
                =
                x
              )
  $.
$}
