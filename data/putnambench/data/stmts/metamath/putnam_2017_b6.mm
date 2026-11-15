$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_b6: the number of ordered 64-tuples of distinct integers from
  1 through 2017 whose Putnam weighted sum is divisible by 2017 has the
  stated factorial value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A tuple is represented by an injective function x from the inclusive
  index interval 0 through 63 into 1 through 2017. The conditional coefficient
  is 1 at indices 0 and 1, and is i thereafter, so the sum is exactly

             x_0 + x_1 + 2 x_2 + ... + 63 x_63.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i x $.

  putnambench-putnam-2017-b6 $a |-
    (
      #
      `
      {
        x e. _V |
        (
          x : ( 0 ... ; 6 3 ) -1-1-> ( 1 ... ; ; ; 2 0 1 7 )
          /\
          ; ; ; 2 0 1 7
          ||
          (
            sum_ i e. ( 0 ... ; 6 3 )
              if (
                i < 2 ,
                ( x ` i ) ,
                ( i x. ( x ` i ) )
              )
          )
        )
      }
    )
    =
    (
      (
        ( ! ` ; ; ; 2 0 1 6 )
        /
        ( ! ` ; ; ; 1 9 5 3 )
      )
      -
      (
        ( ! ` ; 6 3 )
        x.
        ; ; ; 2 0 1 6
      )
    )
  $.
$}
