$(
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_body_S: for every carrier type and natural number n,
  the successor bigop body is the curried function that includes f(n) with
  the binary operation exactly when the Boolean predicate holds at n.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The restricted quantifier h e. _V ranges over every SetMM set, faithfully
  representing the source's arbitrary carrier type; n ranges over NN0.
  LogBigop h n represents bigop H n, and LogBigopBodySucc h n represents
  bigop_body H (S n).

  The nested maps-to expression is the source curried lambda over a Boolean
  predicate p, base value x, binary operation o, and sequence f. The Boolean
  carrier is {0,1}, and the SetMM conditional selects the operation branch
  exactly when p(n) = 1. The final assertion is only the source equality;
  it adds no typing conjuncts. All declarations are unproved $a statement
  encodings, and this database contains no $p proof declaration.
$)

$c LogBigop LogBigopBodySucc $.

log-bigop-syntax $a class ( LogBigop h n ) $.
log-bigop-body-succ-syntax $a class ( LogBigopBodySucc h n ) $.

${
  $d f h n o p x $.

  logipedia-bigops-axiom-bigop-body-s $a |-
    A. h e. _V A. n e. NN0
      ( LogBigopBodySucc h n ) =
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
        )
  $.
$}
