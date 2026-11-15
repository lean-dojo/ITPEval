$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b2: the minimum number of ones in the binary representation
  of a positive multiple of 2023 is 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and NN are set.mm's classes of nonnegative and positive integers.
  The universally quantified function d is characterized by d(0) = 0 and,
  for positive n, by the binary-popcount recurrence: the low binary digit
  plus d(floor(n/2)).

  The conclusion expands the minimum assertion bidirectionally: every
  positive multiple of 2023 has at least three ones, and an internally
  existential positive multiplier attains exactly three. The declaration
  is a single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d d n $.

  putnambench-putnam-2023-b2 $a |-
    A. d e. ( NN0 ^m NN0 )
      (
        A. n e. NN0
          ( d ` n )
          =
          if (
            n = 0 ,
            0 ,
            (
              if (
                ( n mod 2 ) = 1 ,
                1 ,
                0
              )
              +
              ( d ` ( |_ ` ( n / 2 ) ) )
            )
          )
        ->
        (
          A. n e. NN
            3
            <_
            ( d ` ( ( ; ; ; 2 0 2 3 ) x. n ) )
          /\
          E. n e. NN
            ( d ` ( ( ; ; ; 2 0 2 3 ) x. n ) )
            =
            3
        )
      )
  $.
$}
