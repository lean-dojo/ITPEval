$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_aux_mod_aux, catalog title "div_mod.div_aux_mod_aux": for all
  natural numbers p, n, and m, n is the sum of div_aux p n m times the
  successor of m and mod_aux p n m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAux and LogModAux represent the fixed source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. SetMM
  multiplication, addition, and m + 1 represent nat.times, nat.plus, and
  nat.S on the source natural-number domain. Native SetMM equality represents
  the source logic.eq on that domain.

  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogDivAux LogModAux
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-div-aux-syntax $a class ( LogDivAux ) $.
log-mod-aux-syntax $a class ( LogModAux ) $.
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

  logipedia-div-mod-div-aux-mod-aux $a |-
    (
      (
        ( LogDivAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogModAux ) e. ( LogNatToBinaryFunction )
      )
      /\
      A. p e. NN0 A. n e. NN0 A. m e. NN0
        n =
          (
            (
              (
                ( ( ( LogDivAux ) ` p ) ` n )
                ` m
              )
              x. ( m + 1 )
            )
            +
            (
              ( ( ( LogModAux ) ` p ) ` n )
              ` m
            )
          )
    )
  $.
$}
