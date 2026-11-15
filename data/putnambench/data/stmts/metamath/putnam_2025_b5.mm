$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b5 (putnambench__metamath__putnam_2025_b5): for every prime
  p greater than three, the number of descents between consecutive least
  positive modular inverses exceeds p / 4 - 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is SetMM's class of positive natural primes, and 1 ... n is the
  inclusive positive-integer interval. For prime p and k in 1 ... (p - 1),
  the restricted class in P25B5Inv p is a singleton: its member is the
  unique i in 1 ... (p - 1) satisfying k * i congruent to 1 modulo p.
  Taking its union therefore gives exactly ZMod.val of the inverse used by
  the Lean source.

  The filtered interval is the source Finset.Icc 1 (p - 2), and # gives its
  finite cardinality. SetMM division and subtraction on these real numeric
  values make (p / 4) - 1 the same rational bound as in the source. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

$c P25B5Inv $.

p25b5-inv-syntax $a class ( P25B5Inv p ) $.

${
  $d i k p $.

  p25b5-inv-definition $a |- ( P25B5Inv p ) =
    (
      k e. ( 1 ... ( p - 1 ) ) |->
        U. { i e. ( 1 ... ( p - 1 ) ) |
          ( ( k x. i ) mod p ) = 1
        }
    )
  $.
$}

${
  $d k p $.

  putnambench-putnam-2025-b5 $a |- A. p e. Prime
    (
      3 < p
      ->
      (
        ( ( p / 4 ) - 1 )
        <
        (
          #
          `
          { k e. ( 1 ... ( p - 2 ) ) |
            (
              ( ( P25B5Inv p ) ` ( k + 1 ) )
              <
              ( ( P25B5Inv p ) ` k )
            )
          }
        )
      )
    )
  $.
$}
