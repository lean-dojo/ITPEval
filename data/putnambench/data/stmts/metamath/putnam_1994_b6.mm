$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b6: equality modulo 10100 of two sums from the integer
  sequence n(a) = 101a - 100 times 2^a determines the same unordered
  pair of indices between 0 and 99. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class ( ZZ ^m NN0 ) consists of all integer-valued sequences on the
  nonnegative integers. The antecedent retains the source definition of n
  at every index. SetMM's modulo operation accepts integer dividends and a
  positive modulus, so equality of the displayed remainders is exactly the
  source congruence modulo 10100, including when sequence values are negative.

  The interval 0 ... 99 is the inclusive natural interval, and equality of
  { a , b } and { c , d } is equality of the source unordered pairs. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d a b c d i n $.

  putnambench-putnam-1994-b6 $a |-
    A. n e. ( ZZ ^m NN0 )
      (
        A. i e. NN0
          ( n ` i )
          =
          (
            ( ; ; 1 0 1 x. i )
            -
            ( ; ; 1 0 0 x. ( 2 ^ i ) )
          )
        ->
        A. a e. ( 0 ... ; 9 9 )
          A. b e. ( 0 ... ; 9 9 )
            A. c e. ( 0 ... ; 9 9 )
              A. d e. ( 0 ... ; 9 9 )
                (
                  (
                    ( ( ( n ` a ) + ( n ` b ) ) mod ; ; ; ; 1 0 1 0 0 )
                    =
                    ( ( ( n ` c ) + ( n ` d ) ) mod ; ; ; ; 1 0 1 0 0 )
                  )
                  ->
                  { a , b } = { c , d }
                )
      )
  $.
$}
