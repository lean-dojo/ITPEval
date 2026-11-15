$(
  Statement-only formalization of PutnamBench artifact putnam_1963_a2:
  a strictly increasing positive-integer-valued arithmetic function,
  normalized at two and multiplicative on coprime positive inputs, is the
  identity on the positive integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and NN are the set.mm classes of nonnegative and positive integers.
  Thus F : NN0 --> NN combines the source function's natural-number domain
  and codomain with its positivity assumption. Strict increase is stated on
  NN, matching the source interval from one onward, and relative primality
  is expressed by gcd equal to one.

  The final declaration is the single unproved $a statement. This database
  contains no $p proof statement.
$)

${
  $d F i j m n $.
  $d i j $.
  $d m n $.

  putnambench-putnam-1963-a2 $a |- A. F
    (
      (
        (
          F : NN0 --> NN
          /\
          A. i e. NN A. j e. NN
            (
              i < j
              ->
              ( F ` i ) < ( F ` j )
            )
        )
        /\
        (
          ( F ` 2 ) = 2
          /\
          A. m e. NN A. n e. NN
            (
              ( m gcd n ) = 1
              ->
              ( F ` ( m x. n ) )
              =
              ( ( F ` m ) x. ( F ` n ) )
            )
        )
      )
      ->
      A. n e. NN ( F ` n ) = n
    )
  $.
$}
