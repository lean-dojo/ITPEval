$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_b3: the limiting probability, scaled by the square root of the
  sample bound, that the sum of two independent uniform positive integers is
  a perfect square. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each positive integer n, the restricted class consists exactly of the
  ordered pairs in {1,...,n} x {1,...,n} whose coordinate sum is the square
  of a nonnegative integer. Its finite cardinality divided by n^2 is the
  source probability p(n).

  Inlining this defining formula eliminates the source's externally named p
  without changing its quantifier scope. Restricting the displayed sequence
  to positive indices only removes its irrelevant value at zero and
  preserves the limit at infinity. The right side is the explicit solution
  recorded in the ground-truth annotations. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d m n q $.

  putnambench-putnam-1982-b3 $a |-
    (
      n e. NN |->
        (
          (
            (
              #
              `
              {
                q e. ( ( 1 ... n ) X. ( 1 ... n ) ) |
                E. m e. NN0
                  (
                    ( m ^ 2 )
                    =
                    (
                      ( 1st ` q )
                      +
                      ( 2nd ` q )
                    )
                  )
              }
            )
            /
            ( n ^ 2 )
          )
          x.
          ( sqrt ` n )
        )
    )
    ~~>
    (
      ( 4 / 3 )
      x.
      (
        ( sqrt ` 2 )
        -
        1
      )
    )
  $.
$}
