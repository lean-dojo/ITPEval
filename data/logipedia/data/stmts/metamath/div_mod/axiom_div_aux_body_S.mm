$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_div_aux_body_S, catalog title
  "div_mod.axiom_div_aux_body_S": for every natural number p, the
  successor-indexed division auxiliary body is the binary-natural function
  returning zero when m is at most n and otherwise returning the successor
  of div_aux p applied to m minus the successor of n and to n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAux and LogDivAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. SetMM's
  conditional

    if ( ( n + 1 ) <_ m , m - ( n + 1 ) , 0 )

  is exactly truncated natural subtraction m - (n + 1), while the outer
  conditional tests the source Boolean nat.leb m n. Ordinary SetMM equality
  is therefore the source connectives.equal at the binary-function type.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogDivAux LogDivAuxBody
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-div-aux-syntax $a class ( LogDivAux ) $.
log-div-aux-body-syntax $a class ( LogDivAuxBody ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.
log-nat-to-binary-function-syntax $a class
  ( LogNatToBinaryFunction )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( NN0 ^m NN0 ) ^m NN0 )
$.

log-nat-to-binary-function-definition $a |-
  ( LogNatToBinaryFunction ) =
    ( ( LogNatBinaryFunction ) ^m NN0 )
$.

${
  $d m n p $.

  logipedia-div-mod-axiom-div-aux-body-s $a |-
    (
      (
        ( LogDivAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogDivAuxBody ) e. ( LogNatToBinaryFunction )
      )
      /\
      A. p e. NN0
        ( ( LogDivAuxBody ) ` ( p + 1 ) ) =
          (
            m e. NN0 |->
              (
                n e. NN0 |->
                  if (
                    m <_ n ,
                    0 ,
                    (
                      (
                        (
                          ( LogDivAux ) ` p
                        )
                        `
                        if (
                          ( n + 1 ) <_ m ,
                          ( m - ( n + 1 ) ) ,
                          0
                        )
                      )
                      ` n
                    )
                    + 1
                  )
              )
          )
    )
  $.
$}
