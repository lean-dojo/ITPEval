$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b6: an upper bound on the number of length-2018 integer
  sequences with terms in {1, 2, 3, 4, 5, 6, 10} and sum 3860. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ 2018 is the set of indices from 0 through 2017, so
  ZZ ^m ( 0 ..^ 2018 ) is exactly the source type of length-2018
  integer sequences. The disjunction is equivalent to membership in the
  source seven-element set. The restricted class therefore contains exactly
  the sequences whose terms have the prescribed values and whose finite sum
  is 3860, and # is its cardinality.

  The right side is the source real expression
  2^3860 * (2018/2048)^2018. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof declaration.
$)

${
  $d i s $.

  putnambench-putnam-2018-b6 $a |-
    (
      #
      `
      {
        s e. ( ZZ ^m ( 0 ..^ ( ; ; ; 2 0 1 8 ) ) ) |
        (
          A. i e. ( 0 ..^ ( ; ; ; 2 0 1 8 ) )
            (
              ( s ` i ) = 1
              \/
              (
                ( s ` i ) = 2
                \/
                (
                  ( s ` i ) = 3
                  \/
                  (
                    ( s ` i ) = 4
                    \/
                    (
                      ( s ` i ) = 5
                      \/
                      (
                        ( s ` i ) = 6
                        \/
                        ( s ` i ) = ( ; 1 0 )
                      )
                    )
                  )
                )
              )
            )
          /\
          (
            sum_ i e. ( 0 ..^ ( ; ; ; 2 0 1 8 ) )
              ( s ` i )
          )
          =
          ( ; ; ; 3 8 6 0 )
        )
      }
    )
    <_
    (
      ( 2 ^ ( ; ; ; 3 8 6 0 ) )
      x.
      (
        (
          ( ; ; ; 2 0 1 8 )
          /
          ( ; ; ; 2 0 4 8 )
        )
        ^
        ( ; ; ; 2 0 1 8 )
      )
    )
  $.
$}
