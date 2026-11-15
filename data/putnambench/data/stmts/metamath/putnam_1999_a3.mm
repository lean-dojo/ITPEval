$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a3: coefficients of the real power-series expansion of
  1 / (1 - 2x - x^2) satisfy the stated sum-of-two-squares identity.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable a ranges over arbitrary real sequences indexed by NN0.
  The hypothesis internally quantifies a positive radius e and states that,
  throughout the open interval abs(x) < e, the sequence of half-open partial
  sums through indices k < N converges to 1 / (1 - 2x - x^2). This is the
  sequence-limit form of the local power-series equality in all three source
  representations.

  The function f from the sources is inlined using its defining equality.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a e k m n N x $.

  putnambench-putnam-1999-a3 $a |- A. a e. ( RR ^m NN0 )
    (
      E. e e. RR
        (
          0 < e
          /\
          A. x e. RR
            (
              ( abs ` x ) < e
              ->
              (
                N e. NN0 |->
                  sum_ k e. ( 0 ..^ N )
                    (
                      ( a ` k )
                      x.
                      ( x ^ k )
                    )
              )
              ~~>
              (
                1
                /
                (
                  ( 1 - ( 2 x. x ) )
                  -
                  ( x ^ 2 )
                )
              )
            )
        )
      ->
      A. n e. NN0 E. m e. NN0
        (
          ( ( a ` n ) ^ 2 )
          +
          ( ( a ` ( n + 1 ) ) ^ 2 )
        )
        =
        ( a ` m )
    )
  $.
$}
