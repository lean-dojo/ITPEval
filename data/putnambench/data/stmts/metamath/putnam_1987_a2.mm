$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a2: the decimal digit block containing position 10^1987 in
  the concatenation of the positive integers has length 1984. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  I, D, S, and F range over all functions from nonnegative integers to
  nonnegative integers. For positive n, D(n) is characterized as its decimal
  digit count by 10^(D(n)-1) <= n < 10^D(n). The remaining antecedents give
  the starting position I(n) of n's digit block, assign its digit count to
  every position in that block through S, and define F(n) from position 10^n.

  The inclusive interval from 0 through D(i)-1 is exactly the finite-index
  range in the Lean source and the natural interval in the Isabelle source.
  The annotated solution 1984 is inlined in the conclusion. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d D F I S i j n $.

  putnambench-putnam-1987-a2 $a |-
    A. I e. ( NN0 ^m NN0 )
      A. D e. ( NN0 ^m NN0 )
        A. S e. ( NN0 ^m NN0 )
          A. F e. ( NN0 ^m NN0 )
            (
              (
                ( I ` 1 ) = 1
                /\
                A. i e. NN
                  (
                    2 <_ i
                    ->
                    ( I ` i )
                    =
                    (
                      ( I ` ( i - 1 ) )
                      +
                      ( D ` ( i - 1 ) )
                    )
                  )
                /\
                A. i e. NN
                  A. j e. ( 0 ... ( ( D ` i ) - 1 ) )
                    ( S ` ( ( I ` i ) + j ) ) = ( D ` i )
                /\
                A. n e. NN0
                  ( F ` n ) = ( S ` ( ( ; 1 0 ) ^ n ) )
                /\
                A. n e. NN
                  (
                    (
                      ( ; 1 0 )
                      ^
                      ( ( D ` n ) - 1 )
                    )
                    <_
                    n
                    /\
                    n
                    <
                    (
                      ( ; 1 0 )
                      ^
                      ( D ` n )
                    )
                  )
              )
              ->
              ( F ` ; ; ; 1 9 8 7 ) = ; ; ; 1 9 8 4
            )
  $.
$}
