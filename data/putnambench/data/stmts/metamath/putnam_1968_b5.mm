$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_b5: the number of two-by-two matrices over the field of
  residues modulo a prime with trace one and determinant zero is p squared
  plus p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each p in the SetMM class Prime, Z/nZ ` p is the quotient field of
  integers modulo p. The carrier of ( 0 ..^ 2 ) Mat ( Z/nZ ` p ) consists
  exactly of two-by-two matrices indexed by 0 and 1. The first conjunct is
  the trace-one condition using the field addition and unit, and the second
  uses SetMM's native determinant function and field zero.

  Thus the restricted class contains exactly the matrices quantified in the
  Lean and Isabelle sources, and # gives its finite cardinality. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d M p $.

  putnambench-putnam-1968-b5 $a |- A. p e. Prime
    (
      #
      `
      {
        M e. ( Base ` ( ( 0 ..^ 2 ) Mat ( Z/nZ ` p ) ) )
        |
        (
          (
            ( 0 M 0 )
            ( +g ` ( Z/nZ ` p ) )
            ( 1 M 1 )
          )
          =
          ( 1r ` ( Z/nZ ` p ) )
          /\
          (
            (
              ( ( 0 ..^ 2 ) maDet ( Z/nZ ` p ) )
              `
              M
            )
            =
            ( 0g ` ( Z/nZ ` p ) )
          )
        )
      }
      =
      ( ( p ^ 2 ) + p )
    )
  $.
$}
