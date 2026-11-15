$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a2: the integer recurrence a(0) = 1, a(1) = 2, and
  a(n) = 4 a(n-1) - a(n-2) has 181 as an odd prime divisor of a(2015).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m NN0 is the class of all total integer-valued sequences indexed by
  the nonnegative integers. The implication preserves the source's arbitrary
  sequence together with both initial values and the recurrence at every
  natural index n at least 2.

  The explicit numerals ; ; 1 8 1 and ; ; ; 2 0 1 5 are set.mm's decimal
  representations of 181 and 2015. Membership in Odd and Prime and integer
  divisibility express exactly that 181 is an odd prime factor of a(2015).
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a n $.

  putnambench-putnam-2015-a2 $a |- A. a e. ( ZZ ^m NN0 )
    (
      (
        (
          ( a ` 0 ) = 1
          /\
          ( a ` 1 ) = 2
        )
        /\
        A. n e. NN0
          (
            2 <_ n
            ->
            ( a ` n )
            =
            (
              (
                4
                x.
                ( a ` ( n - 1 ) )
              )
              -
              ( a ` ( n - 2 ) )
            )
          )
      )
      ->
      (
        (
          ; ; 1 8 1 e. Odd
          /\
          ; ; 1 8 1 e. Prime
        )
        /\
        ; ; 1 8 1 || ( a ` ; ; ; 2 0 1 5 )
      )
    )
  $.
$}
