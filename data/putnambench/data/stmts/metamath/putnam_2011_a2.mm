$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a2: convergence and evaluation as three halves of the reciprocal
  product series associated with two positive real sequences satisfying the
  stated recurrence and boundedness condition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The sequences a and b are arbitrary NN0-indexed real sequences. The
  zero-based indexing follows the primary Lean formalization: a(0) = b(0) = 1,
  the recurrence starts at n = 1, and the n-th partial sum contains the terms
  indexed by i in 0 ..^ n, with each denominator the product over 0 ... i.
  This is exactly the published one-based series after shifting indices.

  The secondary Rocq source shifts the recurrence and initial values to zero
  but leaves its displayed sum starting at one, thereby omitting the initial
  term 1. The assertion below follows the published problem and the primary
  Lean source, and uses the explicit value 3 / 2 recorded by Rocq and the
  solution annotations. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d a b c i j n $.

  putnambench-putnam-2011-a2 $a |-
    A. a e. ( RR ^m NN0 )
    A. b e. ( RR ^m NN0 )
      (
        (
          (
            (
              A. n e. NN0
                (
                  0 < ( a ` n )
                  /\
                  0 < ( b ` n )
                )
              /\
              (
                ( a ` 0 ) = 1
                /\
                ( b ` 0 ) = 1
              )
            )
            /\
            A. n e. NN0
              (
                1 <_ n
                ->
                ( b ` n )
                =
                (
                  (
                    ( b ` ( n - 1 ) )
                    x.
                    ( a ` n )
                  )
                  -
                  2
                )
              )
          )
          /\
          E. c e. RR
            A. n e. NN0
              ( abs ` ( b ` n ) ) <_ c
        )
        ->
        (
          n e. NN0 |->
            sum_ i e. ( 0 ..^ n )
              (
                1
                /
                (
                  prod_ j e. ( 0 ... i )
                    ( a ` j )
                )
              )
        )
        ~~>
        ( 3 / 2 )
      )
  $.
$}
