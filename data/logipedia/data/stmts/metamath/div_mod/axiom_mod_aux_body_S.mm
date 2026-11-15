$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_mod_aux_body_S, catalog title
  "div_mod.axiom_mod_aux_body_S": for every natural number p, the
  successor-indexed modulus auxiliary body is the binary-natural function
  returning m when m is at most n and otherwise returning mod_aux p applied
  to the truncated difference m minus the successor of n and to n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogModAux and LogModAuxBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. SetMM's
  conditional

    if ( ( n + 1 ) <_ m , m - ( n + 1 ) , 0 )

  is exactly truncated natural subtraction m - (n + 1), while the outer
  conditional tests the source Boolean nat.leb m n. Native SetMM equality
  represents the fixed source connectives.equal relation at this function
  type via the catalogued bidirectional equality correspondence.

  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogModAux LogModAuxBody
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-mod-aux-syntax $a class ( LogModAux ) $.
log-mod-aux-body-syntax $a class ( LogModAuxBody ) $.
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

  logipedia-div-mod-axiom-mod-aux-body-s $a |-
    (
      (
        ( LogModAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogModAuxBody ) e. ( LogNatToBinaryFunction )
      )
      /\
      A. p e. NN0
        ( ( LogModAuxBody ) ` ( p + 1 ) ) =
          (
            m e. NN0 |->
              (
                n e. NN0 |->
                  if (
                    m <_ n ,
                    m ,
                    (
                      (
                        (
                          ( LogModAux ) ` p
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
                  )
              )
          )
    )
  $.
$}
