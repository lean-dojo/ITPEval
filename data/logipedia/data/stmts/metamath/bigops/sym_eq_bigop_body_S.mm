$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_body_S: for every carrier type and natural number n,
  the curried function that includes f(n) with the binary operation exactly
  when the Boolean predicate holds at n is Leibniz equal to the successor
  bigop body. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier h and index n remain arbitrary. Full SetMM function spaces
  encode the source type

    (NN0 -> Bool) -> h -> (h -> h -> h) -> (NN0 -> h) -> h,

  with {0,1} as the Boolean carrier. LogBigop h n represents the source
  bigop at n, and LogBigopBodySucc h n represents bigop_body at S n. The
  nested maps-to expression is the source lambda p, nil, op, f, while the
  SetMM conditional tests p(n) = 1. A predicate on the common function type
  is represented extensionally by a subset q, so the bounded universal
  implication is precisely the source Leibniz equality in its stated
  direction. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c LogBigop LogBigopBodySucc LogBigopBodySuccType $.

log-bigop-syntax $a class ( LogBigop h n ) $.
log-bigop-body-succ-syntax $a class ( LogBigopBodySucc h n ) $.
log-bigop-body-succ-type-syntax $a class ( LogBigopBodySuccType h ) $.

log-bigop-body-succ-type-definition $a |- ( LogBigopBodySuccType h ) =
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
  $d f h n o p q x $.

  logipedia-bigops-sym-eq-bigop-body-s $a |-
    A. h A. n e. NN0
      (
        (
          ( LogBigopBodySucc h n ) e. ( LogBigopBodySuccType h )
          /\
          (
            ( LogBigop h n ) e. ( LogBigopBodySuccType h )
            /\
            (
              p e. ( { 0 , 1 } ^m NN0 ) |->
                (
                  x e. h |->
                    (
                      o e. ( ( h ^m h ) ^m h ) |->
                        (
                          f e. ( h ^m NN0 ) |->
                            if (
                              ( p ` n ) = 1 ,
                              (
                                ( o ` ( f ` n ) )
                                `
                                ( ( ( ( ( LogBigop h n ) ` p ) ` x ) ` o ) ` f )
                              ) ,
                              ( ( ( ( ( LogBigop h n ) ` p ) ` x ) ` o ) ` f )
                            )
                        )
                    )
                )
            ) e. ( LogBigopBodySuccType h )
          )
        )
        /\
        A. q e. ~P ( LogBigopBodySuccType h )
          (
            (
              p e. ( { 0 , 1 } ^m NN0 ) |->
                (
                  x e. h |->
                    (
                      o e. ( ( h ^m h ) ^m h ) |->
                        (
                          f e. ( h ^m NN0 ) |->
                            if (
                              ( p ` n ) = 1 ,
                              (
                                ( o ` ( f ` n ) )
                                `
                                ( ( ( ( ( LogBigop h n ) ` p ) ` x ) ` o ) ` f )
                              ) ,
                              ( ( ( ( ( LogBigop h n ) ` p ) ` x ) ` o ) ` f )
                            )
                        )
                    )
                )
            ) e. q
            ->
            ( LogBigopBodySucc h n ) e. q
          )
      )
  $.
$}
