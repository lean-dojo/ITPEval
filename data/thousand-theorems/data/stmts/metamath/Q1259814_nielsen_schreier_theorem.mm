$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1259814
  (thousand-theorems__metamath__Q1259814), "Nielsen-Schreier theorem": every
  subgroup of an arbitrary free group is itself a free group. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's freeGrp constructs the free group on an arbitrary set of generators,
  and G ~=g H states that the bundled groups G and H are isomorphic. Thus
  existence of I with G ~=g ( freeGrp ` I ) faithfully expresses that G is a
  free group. For H e. ( SubGrp ` G ), the restriction G |`s H is the inherited
  group structure on H. Both generator sets remain existentially quantified,
  and no finiteness restriction is imposed.

  The declaration below is the unproved $a statement corresponding to
  subgroupIsFreeOfIsFree; it adds no $p proof statement.
$)

${
  $d G H I J $.

  thousand-theorems-q1259814-nielsen-schreier $a |- (
    A. G A. H
      (
        (
          (
            G e. Grp
            /\
            E. I G ~=g ( freeGrp ` I )
          )
          /\
          H e. ( SubGrp ` G )
        )
        ->
        E. J ( G |`s H ) ~=g ( freeGrp ` J )
      )
  ) $.
$}
