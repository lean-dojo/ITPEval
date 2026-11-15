$(
  Statement-only formalization of Thousand Theorems corpus artifact Q17005116
  (thousand-theorems__metamath__Q17005116), "Birkhoff's representation
  theorem": the canonical map from a finite distributive lattice to the
  powerset of its sup-irreducible elements is an injective lattice
  homomorphism. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  QBRKSupIrred K is the subtype carrier of the sup-irreducible elements of
  the lattice K. Its defining predicate is exactly the conjunction used by
  mathlib: the element is not a bottom element, and any binary join equal to
  it has one operand equal to it.

  QBRKBirkhoff K is the canonical map taking x to the set of sup-irreducible
  elements below x. SetMM's classical set comprehension makes the source
  DecidablePred dictionary implicit without changing this set or the map.

  The final declaration says that this canonical map is injective and
  preserves binary joins and meets as union and intersection. It is the
  single unproved $a corpus statement. All preceding $a declarations are
  syntax or faithful definitions, and this database contains no $p proof
  statement.
$)

$c QBRKSupIrred QBRKBirkhoff $.

qbrk-sup-irreducible-syntax $a class ( QBRKSupIrred K ) $.
qbrk-birkhoff-map-syntax $a class ( QBRKBirkhoff K ) $.

${
  $d K a x y z $.

  qbrk-sup-irreducible-definition $a |- ( QBRKSupIrred K ) =
    {
      a e. ( Base ` K ) |
        (
          -. A. x e. ( Base ` K ) a ( le ` K ) x
          /\
          A. y e. ( Base ` K ) A. z e. ( Base ` K )
            (
              ( y ( join ` K ) z ) = a
              ->
              ( y = a \/ z = a )
            )
        )
    }
  $.
$}

${
  $d K a x $.

  qbrk-birkhoff-map-definition $a |- ( QBRKBirkhoff K ) =
    (
      x e. ( Base ` K ) |->
        { a e. ( QBRKSupIrred K ) | a ( le ` K ) x }
    )
  $.
$}

${
  $d K x y $.

  thousand-theorems-q17005116-birkhoff-representation $a |-
    A. K
      (
        (
          K e. DLat
          /\
          ( Base ` K ) e. Fin
        )
        ->
        (
          ( QBRKBirkhoff K )
            : ( Base ` K ) -1-1-> ~P ( QBRKSupIrred K )
          /\
          A. x e. ( Base ` K ) A. y e. ( Base ` K )
            (
              (
                ( QBRKBirkhoff K ) ` ( x ( join ` K ) y )
              )
              =
              (
                ( ( QBRKBirkhoff K ) ` x )
                u.
                ( ( QBRKBirkhoff K ) ` y )
              )
              /\
              (
                ( QBRKBirkhoff K ) ` ( x ( meet ` K ) y )
              )
              =
              (
                ( ( QBRKBirkhoff K ) ` x )
                i^i
                ( ( QBRKBirkhoff K ) ` y )
              )
            )
        )
      )
  $.
$}
