$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_body_O: for every carrier type, the curried function
  returning its supplied base value is Leibniz equal to the zero-indexed
  polymorphic bigop body. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h remains arbitrary. The source function type is represented by
  full SetMM function spaces, with {0,1} as the Boolean carrier:

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h.

  The nested maps-to expression is the source lambda p, nil, op, f |-> nil,
  and LogBigopBodyZero h represents bigop_body h 0. A predicate on the
  function type is represented extensionally by a subset q. The bounded
  universal implication is therefore the source definition of Leibniz
  equality in its stated direction. The final declaration is an unproved $a
  statement encoding; this corpus file contains no $p proof declaration.
$)

$c LogBigopBodyZero LogBigopBodyZeroType $.

log-bigop-body-zero-syntax $a class ( LogBigopBodyZero h ) $.
log-bigop-body-zero-type-syntax $a class ( LogBigopBodyZeroType h ) $.

log-bigop-body-zero-type-definition $a |- ( LogBigopBodyZeroType h ) =
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
  $d f h o p q x $.

  logipedia-bigops-sym-eq-bigop-body-o $a |-
    A. h
      (
        (
          (
            p e. ( { 0 , 1 } ^m NN0 ) |->
              (
                x e. h |->
                  (
                    o e. ( ( h ^m h ) ^m h ) |->
                      ( f e. ( h ^m NN0 ) |-> x )
                  )
              )
          ) e. ( LogBigopBodyZeroType h )
          /\
          ( LogBigopBodyZero h ) e. ( LogBigopBodyZeroType h )
        )
        /\
        A. q e. ~P ( LogBigopBodyZeroType h )
          (
            (
              p e. ( { 0 , 1 } ^m NN0 ) |->
                (
                  x e. h |->
                    (
                      o e. ( ( h ^m h ) ^m h ) |->
                        ( f e. ( h ^m NN0 ) |-> x )
                    )
                )
            ) e. q
            ->
            ( LogBigopBodyZero h ) e. q
          )
      )
  $.
$}
