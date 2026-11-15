$(
  Statement-only formalization of Thousand Theorems corpus artifact Q505798
  (thousand-theorems__metamath__Q505798), "Lagrange's theorem (group theory)":
  for every group and subgroup, the Lean natural cardinality of the subgroup
  divides that of the ambient group. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q505798NatCard A is # A when A is finite and 0 otherwise, exactly matching
  Lean's Nat.card convention on finite and infinite types. In SetMM,
  G e. Grp supplies an arbitrary group, H e. ( SubGrp ` G ) says that H is a
  subgroup carrier, and Base ` G is the ambient carrier.

  The final declaration is the single unproved $a corpus statement; the
  auxiliary $a declarations are syntax and the faithful cardinality
  definition. This database contains no $p proof statement.
$)

$c Q505798NatCard $.

q505798-nat-card-syntax $a class ( Q505798NatCard A ) $.

q505798-nat-card-definition $a |- ( Q505798NatCard A ) =
  if ( A e. Fin , ( # ` A ) , 0 )
$.

${
  $d G H $.

  thousand-theorems-q505798-lagrange $a |- (
    A. G A. H
      (
        (
          G e. Grp
          /\
          H e. ( SubGrp ` G )
        )
        ->
        ( Q505798NatCard H ) || ( Q505798NatCard ( Base ` G ) )
      )
  ) $.
$}
