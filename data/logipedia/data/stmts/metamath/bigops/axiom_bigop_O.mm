$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_O: for every carrier type, the zero-indexed polymorphic
  bigop operator equals its body operator as a curried function of Boolean
  predicates, identities, binary operations, and sequences. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary. The two class expressions represent the
  source terms bigop h 0 and bigop_body h 0. Their common type is encoded by
  full SetMM function spaces, with {0,1} as the two-element Boolean carrier:

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h.

  Typing is stated explicitly together with the source equality. All
  declarations are unproved $a statement encodings; this database contains
  no $p proof declaration.
$)

$c LogBigopZero LogBigopBodyZero LogBigopZeroType $.

log-bigop-zero-syntax $a class ( LogBigopZero h ) $.
log-bigop-body-zero-syntax $a class ( LogBigopBodyZero h ) $.
log-bigop-zero-type-syntax $a class ( LogBigopZeroType h ) $.

log-bigop-zero-type-definition $a |- ( LogBigopZeroType h ) =
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

logipedia-bigops-axiom-bigop-o $a |-
  A. h
    (
      (
        ( LogBigopZero h ) e. ( LogBigopZeroType h )
        /\
        ( LogBigopBodyZero h ) e. ( LogBigopZeroType h )
      )
      /\
      ( LogBigopZero h ) = ( LogBigopBodyZero h )
    )
$.
