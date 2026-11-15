$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_a2: convergence of an eight-periodic signed harmonic series
  is equivalent to having four positive and four negative signs in each
  period. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is an arbitrary real-valued function on the eight indices 0 through 7,
  and the antecedent requires every value to be either 1 or -1. Thus A
  represents exactly one repeating block of signs. For n in NN0, the mapping

    n |-> sum_ i e. ( 1 ... n ) ( ( A ` ( i mod 8 ) ) / i )

  is the source sequence of partial sums. Each occurrence of convergence
  keeps its real limit existentially quantified. The cardinality expression
  counts the positive signs, so equality to 4 is equivalent to balance.

  The two implications state respectively that balance is sufficient and
  necessary for convergence. This is the source answer value True inlined
  into the displayed biconditional. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A B i n $.

  putnambench-putnam-1973-a2 $a |- A. A e. ( RR ^m ( 0 ... 7 ) )
    (
      A. i e. ( 0 ... 7 )
        (
          ( A ` i ) = 1
          \/
          ( A ` i ) = ( -u 1 )
        )
      ->
      (
        (
          (
            #
            `
            { i e. ( 0 ... 7 ) | ( A ` i ) = 1 }
          )
          =
          4
          ->
          E. B e. RR
            (
              n e. NN0 |->
                sum_ i e. ( 1 ... n )
                  ( ( A ` ( i mod 8 ) ) / i )
            )
            ~~>
            B
        )
        /\
        (
          E. B e. RR
            (
              n e. NN0 |->
                sum_ i e. ( 1 ... n )
                  ( ( A ` ( i mod 8 ) ) / i )
            )
            ~~>
            B
          ->
          (
            #
            `
            { i e. ( 0 ... 7 ) | ( A ` i ) = 1 }
          )
          =
          4
        )
      )
    )
  $.
$}
