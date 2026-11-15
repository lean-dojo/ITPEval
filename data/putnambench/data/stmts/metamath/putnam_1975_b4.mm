$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_b4: no topologically closed subset of the real unit circle
  contains exactly one point from each antipodal pair. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  P75B4R2 is the real coordinate plane, P75B4Top is its standard finite
  product topology, and P75B4Circle is the unit circle. P75B4Antipode maps
  each plane point to its coordinatewise negative.

  The source's solution proposition is identified as False, so the final
  unproved $a assertion is the negation of the internally existential
  closed subset B. Its exclusive alternatives state that B contains
  exactly one member of every antipodal pair on the circle. This database
  contains no $p proof statement.
$)

$c P75B4I P75B4R2 P75B4Top P75B4Circle P75B4Antipode $.

p75b4-index-syntax $a class P75B4I $.
p75b4-plane-syntax $a class P75B4R2 $.
p75b4-topology-syntax $a class P75B4Top $.
p75b4-circle-syntax $a class P75B4Circle $.
p75b4-antipode-syntax $a class ( P75B4Antipode A ) $.

p75b4-index-definition $a |- P75B4I = ( 1 ... 2 ) $.

p75b4-plane-definition $a |- P75B4R2 = ( RR ^m P75B4I ) $.

p75b4-topology-definition $a |- P75B4Top =
  (
    Xt_ `
      ( P75B4I X. { ( topGen ` ran (,) ) } )
  )
$.

p75b4-circle-definition $a |- P75B4Circle = {
  z e. P75B4R2 |
    ( ( ( z ` 1 ) ^ 2 ) + ( ( z ` 2 ) ^ 2 ) ) = 1
} $.

${
  $d A j $.

  p75b4-antipode-definition $a |- (
    P75B4Antipode A
  ) = (
    j e. P75B4I |->
      ( -u ( A ` j ) )
  ) $.
$}

${
  $d B z $.

  putnambench-putnam-1975-b4 $a |- -.
    E. B e. ~P P75B4R2
      (
        (
          B C_ P75B4Circle
          /\
          B e. ( Clsd ` P75B4Top )
        )
        /\
        A. z e. P75B4Circle
          (
            (
              z e. B
              /\
              -. ( P75B4Antipode z ) e. B
            )
            \/
            (
              -. z e. B
              /\
              ( P75B4Antipode z ) e. B
            )
          )
      )
  $.
$}
