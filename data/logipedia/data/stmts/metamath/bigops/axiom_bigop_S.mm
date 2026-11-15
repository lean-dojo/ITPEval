$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_S: for every carrier type and natural number n, the
  polymorphic bigop operator at the successor of n equals its body operator
  as a curried function of Boolean predicates, identities, binary operations,
  and sequences. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h and index n remain arbitrary. The two class expressions
  represent the source terms bigop h (S n) and bigop_body h (S n). Their
  common type is encoded by full SetMM function spaces, with {0,1} as the
  two-element Boolean carrier:

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h.

  Typing is stated explicitly together with the source equality. All
  declarations are unproved $a statement encodings; this database contains
  no $p proof declaration.
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

logipedia-bigops-axiom-bigop-s $a |-
  A. h A. n e. NN0
    (
      (
        ( LogBigopSucc h n ) e. ( LogBigopSuccType h )
        /\
        ( LogBigopBodySucc h n ) e. ( LogBigopSuccType h )
      )
      /\
      ( LogBigopSucc h n ) = ( LogBigopBodySucc h n )
    )
$.
