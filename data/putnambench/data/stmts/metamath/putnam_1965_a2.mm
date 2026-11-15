$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a2:
  the finite binomial-coefficient identity equating a sum of squared
  rational terms to a normalized binomial coefficient for every positive
  integer. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The summation index runs from zero through floor((n - 1) / 2), exactly as
  in the source natural-number bound. Within that range, the displayed
  subtractions coincide with natural subtraction. The final declaration is
  the single unproved $a corpus statement.
$)

${
  $d n r $.

  putnambench-putnam-1965-a2 $a |- A. n e. NN
    (
      sum_ r e. ( 0 ... ( |_ ` ( ( n - 1 ) / 2 ) ) )
        (
          (
            (
              ( n - ( 2 x. r ) )
              x.
              ( n _C r )
            )
            /
            n
          )
          ^ 2
        )
      =
      (
        (
          ( ( 2 x. n ) - 2 )
          _C
          ( n - 1 )
        )
        /
        n
      )
    )
  $.
$}
