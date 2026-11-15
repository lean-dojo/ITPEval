$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.eq_bigop_O: for every carrier type, the zero-indexed polymorphic
  bigop operator is Leibniz equal to its body operator as a curried function
  of Boolean predicates, identities, binary operations, and sequences. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary. The two class expressions represent the
  source terms bigop h 0 and bigop_body h 0. Their common type is encoded by
  full SetMM function spaces, with {0,1} as the Boolean carrier:

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h.

  A predicate on this function type is represented extensionally by a subset
  p. The bounded universal implication is therefore the source definition of
  Leibniz equality: every predicate holding of bigop h 0 also holds of
  bigop_body h 0. The final declaration is an unproved $a statement encoding;
  this corpus file adds no $p proof declaration.
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

${
  $d h p $.

  logipedia-bigops-eq-bigop-o $a |-
    A. h
      (
        (
          ( LogBigopZero h ) e. ( LogBigopZeroType h )
          /\
          ( LogBigopBodyZero h ) e. ( LogBigopZeroType h )
        )
        /\
        A. p e. ~P ( LogBigopZeroType h )
          (
            ( LogBigopZero h ) e. p
            ->
            ( LogBigopBodyZero h ) e. p
          )
      )
  $.
$}
