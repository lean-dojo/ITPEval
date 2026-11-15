$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_b1: an integer-valued sequence defined by parity recurrences
  has the sum from 1 through 2013 of c(n)c(n+2) equal to -1. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ZZ are set.mm's nonnegative-integer and integer classes. Thus c
  ranges over exactly the source functions from natural numbers to integers.
  Quantifying the recurrence index over NN is equivalent to the source guard
  n > 0. The interval 1 ... 2013 is inclusive, so the finite sum has exactly
  the source's terms.

  The right side inlines the solution annotation -1, also given explicitly by
  the Rocq source. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d c n $.

  putnambench-putnam-2013-b1 $a |-
    A. c e. ( ZZ ^m NN0 )
      (
        (
          (
            ( c ` 1 ) = 1
            /\
            A. n e. NN
              ( c ` ( 2 x. n ) ) = ( c ` n )
          )
          /\
          A. n e. NN
            ( c ` ( ( 2 x. n ) + 1 ) )
            =
            (
              ( ( -u 1 ) ^ n )
              x.
              ( c ` n )
            )
        )
        ->
        (
          sum_ n e. ( 1 ... ; ; ; 2 0 1 3 )
            (
              ( c ` n )
              x.
              ( c ` ( n + 2 ) )
            )
        )
        =
        ( -u 1 )
      )
  $.
$}
