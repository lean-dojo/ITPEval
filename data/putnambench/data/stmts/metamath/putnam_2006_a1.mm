$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_a1: the three-dimensional Lebesgue volume of the real region
  defined by (x^2 + y^2 + z^2 + 8)^2 <= 36(x^2 + y^2), equated to the
  specified real solution constant. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P06A1R3 is real coordinate three-space, represented by real-valued
  functions on the three-element interval 0 ..^ 3. P06A1Region is exactly the set
  of points satisfying the source polynomial inequality, with coordinates
  0, 1, and 2 corresponding to x, y, and z. P06A1Volume is its
  three-dimensional Lebesgue measure through set.mm's finite-dimensional
  volume function voln.

  The final equality uses the resolved volume 6 * pi^2 from the source
  annotation. Every declaration is an unproved $a statement encoding, and
  this database contains no $p proof statement.
$)

$c P06A1R3 P06A1Region P06A1Volume $.

p06a1-space-syntax $a class P06A1R3 $.
p06a1-region-syntax $a class P06A1Region $.
p06a1-volume-syntax $a class P06A1Volume $.

p06a1-space-definition $a |- P06A1R3 = ( RR ^m ( 0 ..^ 3 ) ) $.

p06a1-region-definition $a |- P06A1Region = {
    p e. P06A1R3 |
      (
        (
          (
            (
              (
                ( p ` 0 ) ^ 2
              )
              +
              (
                ( p ` 1 ) ^ 2
              )
            )
            +
            (
              ( p ` 2 ) ^ 2
            )
          )
          +
          8
        )
        ^ 2
      )
      <_
      (
        ( 6 x. 6 )
        x.
        (
          (
            ( p ` 0 ) ^ 2
          )
          +
          (
            ( p ` 1 ) ^ 2
          )
        )
      )
} $.

p06a1-volume-definition $a |- P06A1Volume = (
  ( voln ` ( 0 ..^ 3 ) )
  `
  P06A1Region
) $.

putnambench-putnam-2006-a1 $a |-
  P06A1Volume = ( 6 x. ( _pi ^ 2 ) )
$.
