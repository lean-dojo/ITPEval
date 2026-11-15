$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b4: an integer polynomial injective on residue
  representatives modulo the square of a prime is injective on residue
  representatives modulo its cube. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is SetMM's ring of arbitrary finite-support
  univariate polynomials over the integers, and eval1 evaluates such a
  polynomial at an integer. For a natural prime p, ( 0 ..^ ( p ^ k ) ) is
  exactly the set of representatives from 0 through p^k - 1. Equality of
  the displayed remainders is integer congruence modulo p^k.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d h i j p $.

  putnambench-putnam-2008-b4 $a |-
    A. p e. Prime
      A. h e. ( Base ` ( Poly1 ` ZZring ) )
        (
          A. i e. ( 0 ..^ ( p ^ 2 ) )
            A. j e. ( 0 ..^ ( p ^ 2 ) )
              (
                (
                  (
                    ( ( ( eval1 ` ZZring ) ` h ) ` i )
                    mod
                    ( p ^ 2 )
                  )
                  =
                  (
                    ( ( ( eval1 ` ZZring ) ` h ) ` j )
                    mod
                    ( p ^ 2 )
                  )
                )
                ->
                i = j
              )
          ->
          A. i e. ( 0 ..^ ( p ^ 3 ) )
            A. j e. ( 0 ..^ ( p ^ 3 ) )
              (
                (
                  (
                    ( ( ( eval1 ` ZZring ) ` h ) ` i )
                    mod
                    ( p ^ 3 )
                  )
                  =
                  (
                    ( ( ( eval1 ` ZZring ) ` h ) ` j )
                    mod
                    ( p ^ 3 )
                  )
                )
                ->
                i = j
              )
        )
  $.
$}
