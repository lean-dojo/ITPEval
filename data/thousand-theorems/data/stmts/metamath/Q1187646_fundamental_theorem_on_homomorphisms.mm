$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1187646
  (thousand-theorems__metamath__Q1187646), "Fundamental theorem on
  homomorphisms": every homomorphism between arbitrary groups induces a group
  isomorphism from the quotient of its domain by its kernel to its range in
  the codomain. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp and H e. Grp supply arbitrary bundled groups, and
  F e. ( G GrpHom H ) supplies an arbitrary homomorphism. The inverse image
  `' F " { ( 0g ` H ) } is its kernel, G /s ( G ~QG N ) is the quotient
  group by a normal subgroup N, H |`s ran F equips the range with the
  restricted codomain group structure, and ~=g is group isomorphism.

  The declaration below is the unproved $a statement corresponding to
  QuotientGroup.quotientKerEquivRange; it adds no $p proof statement.
$)

${
  $d F G H $.

  thousand-theorems-q1187646-fundamental-theorem-on-homomorphisms $a |- (
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
