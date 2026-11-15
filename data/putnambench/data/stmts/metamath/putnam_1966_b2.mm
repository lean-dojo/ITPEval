$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b2:
  among any ten consecutive positive-starting integers, one is relatively
  prime to each of the other nine. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The set.mm interval ( n ... ( n + 9 ) ) is the inclusive integer set from
  n through n + 9, exactly expanding the source definition of S n. Equality
  of the integer gcd with one expresses relative primality.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k m n $.

  putnambench-putnam-1966-b2 $a |-
    A. n e. ZZ
      (
        0 < n
        ->
        E. k e. ( n ... ( n + 9 ) )
          A. m e. ( n ... ( n + 9 ) )
            (
              k =/= m
              ->
              ( m gcd k ) = 1
            )
      )
  $.
$}
