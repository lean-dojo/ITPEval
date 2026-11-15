$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_S: for every carrier type and natural number n, the
  successor-indexed polymorphic bigop body operator is Leibniz equal to the
  bigop operator as a curried function of Boolean predicates, identities,
  binary operations, and sequences. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h and index n remain arbitrary. The two class expressions
  represent the source terms bigop_body h (S n) and bigop h (S n). Their
  common type is encoded by full SetMM function spaces, with {0,1} as the
  Boolean carrier:

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h.

  A predicate on this function type is represented extensionally by a subset
  p. The bounded universal implication is therefore the source definition of
  Leibniz equality: every predicate holding of bigop_body h (S n) also holds
  of bigop h (S n). The final declaration is an unproved $a statement
  encoding; this corpus file adds no $p proof declaration.
$)

$c LogBigopSucc LogBigopBodySucc LogBigopSuccType $.

log-bigop-succ-syntax $a class ( LogBigopSucc h n ) $.
log-bigop-body-succ-syntax $a class ( LogBigopBodySucc h n ) $.
log-bigop-succ-type-syntax $a class ( LogBigopSuccType h ) $.

log-bigop-succ-type-definition $a |- ( LogBigopSuccType h ) =
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
  $d h n p $.

  logipedia-bigops-sym-eq-bigop-s $a |-
    A. h A. n e. NN0
      (
        (
          ( LogBigopBodySucc h n ) e. ( LogBigopSuccType h )
          /\
          ( LogBigopSucc h n ) e. ( LogBigopSuccType h )
        )
        /\
        A. p e. ~P ( LogBigopSuccType h )
          (
            ( LogBigopBodySucc h n ) e. p
            ->
            ( LogBigopSucc h n ) e. p
          )
      )
  $.
$}
