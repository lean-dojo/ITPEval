$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a4:
  eventual periodicity of a bounded integer sequence satisfying a fourth-order
  rational recurrence with nonzero denominator. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m NN0 is the class of total integer-valued sequences indexed by the
  nonnegative integers. Since every sequence value is an integer, the field
  quotient in the recurrence is required to equal that integer exactly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B T N c n $.

  putnambench-putnam-1964-a4 $a |- A. A e. ( ZZ ^m NN0 )
    (
      (
        E. B e. ZZ E. T e. ZZ
          A. n e. NN0
            (
              B <_ ( A ` n )
              /\
              ( A ` n ) <_ T
            )
        /\
        A. n e. NN0
          (
            4 <_ n
            ->
            (
              ( A ` n ) =
                (
                  (
                    ( A ` ( n - 1 ) )
                    +
                    (
                      ( A ` ( n - 2 ) )
                      +
                      (
                        ( A ` ( n - 3 ) )
                        x.
                        ( A ` ( n - 4 ) )
                      )
                    )
                  )
                  /
                  (
                    (
                      ( A ` ( n - 1 ) )
                      x.
                      ( A ` ( n - 2 ) )
                    )
                    +
                    (
                      ( A ` ( n - 3 ) )
                      +
                      ( A ` ( n - 4 ) )
                    )
                  )
                )
              /\
              (
                (
                  ( A ` ( n - 1 ) )
                  x.
                  ( A ` ( n - 2 ) )
                )
                +
                (
                  ( A ` ( n - 3 ) )
                  +
                  ( A ` ( n - 4 ) )
                )
              ) =/= 0
            )
          )
      )
      ->
      E. N e. NN0 E. c e. NN0
        (
          0 < c
          /\
          A. n e. NN0
            (
              N <_ n
              ->
              ( A ` ( n + c ) ) = ( A ` n )
            )
        )
    )
  $.
$}
