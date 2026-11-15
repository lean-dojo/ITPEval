$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1065966
  (thousand-theorems__metamath__Q1065966), "Isomorphism theorem": the first,
  second, and third isomorphism theorems for arbitrary groups, homomorphisms,
  subgroups, and normal subgroups. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's relation G ~=g H means that the two bundled groups are isomorphic.
  The restriction G |`s H equips a subgroup carrier H with the inherited group
  structure, and G /s ( G ~QG N ) is the quotient group by a normal subgroup N.

  In the second assertion, H i^i N is the subgroup intersection and
  H ( LSSum ` G ) N is the subgroup product HN. In the third assertion, the
  image of M under x |-> [ x ] ( G ~QG N ) is the subgroup M / N of G / N.

  The three final $a assertions correspond, in source order, to
  QuotientGroup.quotientKerEquivRange,
  QuotientGroup.quotientInfEquivProdNormalQuotient, and
  QuotientGroup.quotientQuotientEquivQuotient. They are unproved and add no
  $p proof statements.
$)

${
  $d F G H $.

  thousand-theorems-q1065966-quotient-ker-equiv-range $a |- (
    A. G A. H A. F
      (
        (
          G e. Grp
          /\
          H e. Grp
          /\
          F e. ( G GrpHom H )
        )
        ->
        (
          G /s
          (
            G ~QG
            ( `' F " { ( 0g ` H ) } )
          )
        )
        ~=g
        ( H |`s ran F )
      )
  ) $.
$}

${
  $d G H N $.

  thousand-theorems-q1065966-quotient-inf-equiv-prod-normal-quotient $a |- (
    A. G A. H A. N
      (
        (
          G e. Grp
          /\
          H e. ( SubGrp ` G )
          /\
          N e. ( NrmSGrp ` G )
        )
        ->
        (
          (
            ( G |`s H ) /s
            ( ( G |`s H ) ~QG ( H i^i N ) )
          )
          ~=g
          (
            ( G |`s ( H ( LSSum ` G ) N ) ) /s
            (
              ( G |`s ( H ( LSSum ` G ) N ) )
              ~QG
              N
            )
          )
        )
      )
  ) $.
$}

${
  $d G M N x $.

  thousand-theorems-q1065966-quotient-quotient-equiv-quotient $a |- (
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
