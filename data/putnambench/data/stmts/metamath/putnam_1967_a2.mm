$(
  Statement-only formalization of PutnamBench artifact putnam_1967_a2:
  the recurrence and exponential generating function for the number of
  symmetric nonnegative-integer matrices whose column sums are one. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The index set 0 ..^ n is {0,...,n-1}. Thus a matrix is represented exactly
  as a function from (0 ..^ n) X. (0 ..^ n) to NN0. The restricted class in
  the cardinality expression imposes symmetry and column sum one.

  S is integer-valued as in the Lean and Isabelle sources. Its value at zero
  and every positive index is fixed to a natural-number cardinality, so this
  is equivalent to the natural-valued sequence in the Rocq source. The
  infinite sum and exp are set.mm's real-series sum and real exponential.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A S i j n x $.

  putnambench-putnam-1967-a2 $a |- A. S e. ( ZZ ^m NN0 )
    (
      (
        ( S ` 0 ) = 1
        /\
        A. n e. NN
          ( S ` n )
          =
          (
            #
            `
            { A e.
              (
                NN0
                ^m
                ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
              )
              |
              (
                A. i e. ( 0 ..^ n )
                  A. j e. ( 0 ..^ n )
                    ( A ` <. i , j >. ) = ( A ` <. j , i >. )
                /\
                A. j e. ( 0 ..^ n )
                  (
                    sum_ i e. ( 0 ..^ n )
                      ( A ` <. i , j >. )
                  )
                  =
                  1
              )
            }
          )
      )
      ->
      (
        A. n e. NN
          ( S ` ( n + 1 ) )
          =
          (
            ( S ` n )
            +
            ( n x. ( S ` ( n - 1 ) ) )
          )
        /\
        A. x e. RR
          (
            sum_ n e. NN0
              (
                ( S ` n )
                x.
                (
                  ( x ^ n )
                  /
                  ( ! ` n )
                )
              )
          )
          =
          (
            exp
            `
            (
              x
              +
              ( ( x ^ 2 ) / 2 )
            )
          )
      )
    )
  $.
$}
