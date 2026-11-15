$(
  Statement-only formalization of PutnamBench artifact putnam_1963_b2:
  density in the positive real numbers of the set of products 2^m 3^n
  with integer exponents m and n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class RR is the real line, ZZ is the set of integers, and
  ( TopOpen ` RRfld ) is the standard topology on RR. The final unproved
  $a assertion inlines the source definition of S and states that every
  positive real belongs to its topological closure.
$)

${
  $d m n x y $.

  putnambench-putnam-1963-b2 $a |- A. x e. RR
    (
      0 < x
      ->
      x e.
        (
          ( cls ` ( TopOpen ` RRfld ) )
          `
          { y e. RR |
            E. m e. ZZ E. n e. ZZ
              y = ( ( 2 ^ m ) x. ( 3 ^ n ) )
          }
        )
    )
  $.
$}
