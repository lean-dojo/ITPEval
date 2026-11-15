$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a2: the units digit of the floor of
  10^20000 divided by 10^100 + 3 is 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's |_ operation is real floor, and mod is natural-number remainder.
  The displayed quotient is positive, so its floor is a nonnegative integer;
  taking its remainder modulo 10 therefore gives exactly its units digit.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

putnambench-putnam-1986-a2 $a |-
  (
    (
      (
        |_ `
        (
          ( ; 1 0 ^ ; ; ; ; 2 0 0 0 0 )
          /
          ( ( ; 1 0 ^ ; ; 1 0 0 ) + 3 )
        )
      )
      mod
      ; 1 0
    )
    =
    3
  )
$.
