$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_b5: the thousandth digit after the decimal point of the
  square root of the 1998-digit decimal repunit is 1. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The source parameter N is uniquely fixed as the sum of 10^i for
  0 <= i <= 1997, so it is inlined below. Multiplication by 10^1000,
  integer floor, and reduction modulo 10 select exactly the requested
  decimal digit. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

putnambench-putnam-1998-b5 $a |-
  (
    (
      ( |_ `
        (
          ( ; 1 0
            ^
            ; ; ; 1 0 0 0
          )
          x.
          (
            sqrt
            `
            (
              sum_ i e. ( 0 ... ; ; ; 1 9 9 7 )
                ( ; 1 0 ^ i )
            )
          )
        )
      )
      mod
      ; 1 0
    )
    =
    1
  )
$.
