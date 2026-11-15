$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b5: a complex 2n-by-n matrix whose nonzero left-kernel
  vectors cannot be entirely real has a real-part map surjective onto
  all real 2n-vectors. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The zero-based carriers 0 ..^ n and 0 ..^ ( 2 x. n ) represent Fin n
  and Fin (2*n). The matrix M is a total row-indexed family of total
  column functions. Both matrix products from the sources are expanded
  as finite sums: z times M in the hypothesis and M times w in the
  conclusion. Re and Im are SetMM's real- and imaginary-part functions.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d M i j n r w z $.

  putnambench-putnam-1987-b5 $a |-
    A. n e. NN
      A. M e.
        (
          ( CC ^m ( 0 ..^ n ) )
          ^m
          ( 0 ..^ ( 2 x. n ) )
        )
        (
          (
            A. z e. ( CC ^m ( 0 ..^ ( 2 x. n ) ) )
              (
                A. j e. ( 0 ..^ n )
                  (
                    sum_ i e. ( 0 ..^ ( 2 x. n ) )
                      (
                        ( z ` i )
                        x.
                        ( ( M ` i ) ` j )
                      )
                  )
                  =
                  0
                ->
                (
                  -. A. i e. ( 0 ..^ ( 2 x. n ) )
                    ( z ` i ) = 0
                  ->
                  E. i e. ( 0 ..^ ( 2 x. n ) )
                    ( Im ` ( z ` i ) ) =/= 0
                )
              )
          )
          ->
          A. r e. ( RR ^m ( 0 ..^ ( 2 x. n ) ) )
            E. w e. ( CC ^m ( 0 ..^ n ) )
              A. i e. ( 0 ..^ ( 2 x. n ) )
                (
                  Re
                  `
                  (
                    sum_ j e. ( 0 ..^ n )
                      (
                        ( ( M ` i ) ` j )
                        x.
                        ( w ` j )
                      )
                  )
                )
                =
                ( r ` i )
        )
  $.
$}
