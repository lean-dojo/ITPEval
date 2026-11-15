$(
  Statement-only formalization of Thousand Theorems corpus artifact Q765987
  (thousand-theorems__metamath__Q765987), "Heine-Cantor theorem": every
  continuous function from a compact uniform space to an arbitrary uniform
  space is uniformly continuous. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W and V range over SetMM's native class UnifSp of arbitrary uniform spaces.
  Their TopOpen components are exactly the topologies induced by their
  uniform structures. Thus ( TopOpen ` W ) e. Comp is the source compactness
  assumption, membership in ( ( TopOpen ` W ) Cn ( TopOpen ` V ) ) is
  continuity of the total function F, and membership in
  ( ( UnifSt ` W ) uCn ( UnifSt ` V ) ) is uniform continuity.

  The final declaration is the single unproved corpus $a statement. This
  database contains no $p proof statement.
$)

${
  $d F V W $.

  thousand-theorems-q765987-heine-cantor $a |-
    A. W e. UnifSp
      A. V e. UnifSp
        A. F
          (
            (
              ( TopOpen ` W ) e. Comp
              /\
              F e. ( ( TopOpen ` W ) Cn ( TopOpen ` V ) )
            )
            ->
            F e. ( ( UnifSt ` W ) uCn ( UnifSt ` V ) )
          )
  $.
$}
