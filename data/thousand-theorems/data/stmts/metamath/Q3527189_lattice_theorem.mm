$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527189
  (thousand-theorems__metamath__Q3527189), "Lattice theorem": for an arbitrary
  group G and normal subgroups N contained in M, the quotient of G / N by
  M / N is isomorphic to G / M. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's expression G /s ( G ~QG N ) is the quotient group of G by the
  normal subgroup N, and G ~=g H states that the bundled groups G and H are
  isomorphic. The image of M under x |-> [ x ] ( G ~QG N ) is the subgroup
  M / N of G / N.

  The final $a assertion is the unproved statement corresponding to
  QuotientGroup.quotientQuotientEquivQuotient. This database contains no $p
  proof statement.
$)

${
  $d G M N x $.

  thousand-theorems-q3527189-lattice-theorem $a |- (
    A. G A. N A. M
      (
        (
          G e. Grp
          /\
          N e. ( NrmSGrp ` G )
          /\
          M e. ( NrmSGrp ` G )
          /\
          N C_ M
        )
        ->
        (
          (
            ( G /s ( G ~QG N ) ) /s
            (
              ( G /s ( G ~QG N ) )
              ~QG
              (
                (
                  x e. ( Base ` G )
                  |->
                  [ x ] ( G ~QG N )
                )
                " M
              )
            )
          )
          ~=g
          ( G /s ( G ~QG M ) )
        )
      )
  ) $.
$}
