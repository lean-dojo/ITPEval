$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.sym_eq_mod_aux_body_S
  (logipedia__metamath__div_mod.sym_eq_mod_aux_body_S), catalog title
  "div_mod.sym_eq_mod_aux_body_S": for every natural number p, Leibniz
  equality relates the binary-natural function returning m when m is at most
  n and otherwise returning mod_aux p at m minus the successor of n and at n
  to the successor-indexed modulus auxiliary body. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  LogModAux and LogModAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. SetMM's inner
  conditional

    if ( ( n + 1 ) <_ m , m - ( n + 1 ) , 0 )

  is exactly truncated natural subtraction m - (n + 1), while the outer
  conditional tests the source Boolean nat.leb m n. A predicate on the
  binary-function type is represented extensionally by a subset q. Therefore
  the bounded universal implication is exactly the source definition of
  leibniz.leibniz in its stated direction. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
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
  $d m n p q $.

  logipedia-div-mod-sym-eq-mod-aux-body-s $a |-
    (
      (
        ( LogModAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogModAuxBody ) e. ( LogNatToBinaryFunction )
      )
      /\
      A. p e. NN0
        (
          (
            m e. NN0 |->
              (
                n e. NN0 |->
                  if (
                    m <_ n ,
                    m ,
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
          ) e. ( LogNatBinaryFunction )
          /\
          A. q e. ~P ( LogNatBinaryFunction )
            (
              (
                m e. NN0 |->
                  (
                    n e. NN0 |->
                      if (
                        m <_ n ,
                        m ,
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
              ) e. q
              ->
              ( ( LogModAuxBody ) ` ( p + 1 ) ) e. q
            )
        )
    )
  $.
$}
