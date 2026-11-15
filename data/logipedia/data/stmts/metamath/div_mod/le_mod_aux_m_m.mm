$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.le_mod_aux_m_m
  (logipedia__metamath__div_mod.le_mod_aux_m_m), catalog title
  "div_mod.le_mod_aux_m_m": for all natural numbers p, n, and m, if n is at
  most p, then mod_aux p n m is at most m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogModAux represents the fixed source constant of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. Restricted
  quantifiers over NN0 preserve the three source natural-number domains, and
  SetMM's native order on NN0 represents nat.le.

  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogModAux
  LogNatBinaryFunction LogNatToBinaryFunction
$.

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

  logipedia-div-mod-le-mod-aux-m-m $a |-
    (
      ( LogModAux ) e. ( LogNatToBinaryFunction )
      /\
      A. p e. NN0 A. n e. NN0 A. m e. NN0
        (
          n <_ p
          ->
          (
            ( ( ( LogModAux ) ` p ) ` n )
            ` m
          )
          <_
          m
        )
    )
  $.
$}
