$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_a5: every nonempty real interval contains a nonempty open
  subinterval disjoint from the set of sums of 1994 terms of a positive
  real sequence tending to zero, taken at increasing indices. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The sequence r ranges over all functions from NN0 to RR, and S ranges over
  all subsets of RR. The epsilon-threshold clause is the atTop limit of r at
  zero. The index set 0 ... 1993 has exactly 1994 elements, so functions i
  from that set to NN0 with the displayed strict-order condition are exactly
  the increasing index selections in the source.

  The equality defining S preserves the source set of all corresponding
  finite sums. The conclusion uses set.mm's open real interval and requires
  its intersection with S to be empty. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d N S a b c d e i j k n r x $.

  putnambench-putnam-1994-a5 $a |-
    A. r e. ( RR ^m NN0 )
    A. S e. ~P RR
      (
        (
          A. n e. NN0 0 < ( r ` n )
          /\
          (
            A. e e. RR
              (
                0 < e
                ->
                E. N e. NN0
                  A. n e. NN0
                    (
                      N <_ n
                      ->
                      ( abs ` ( r ` n ) ) < e
                    )
              )
            /\
            S
            =
            {
              x e. RR |
              E. i e.
                ( NN0 ^m ( 0 ... ; ; ; 1 9 9 3 ) )
                (
                  A. j e. ( 0 ... ; ; ; 1 9 9 3 )
                    A. k e. ( 0 ... ; ; ; 1 9 9 3 )
                      (
                        j < k
                        ->
                        ( i ` j ) < ( i ` k )
                      )
                  /\
                  x
                  =
                  (
                    sum_ j e. ( 0 ... ; ; ; 1 9 9 3 )
                      ( r ` ( i ` j ) )
                  )
                )
            }
          )
        )
        ->
        A. a e. RR A. b e. RR
          (
            a < b
            ->
            E. c e. RR E. d e. RR
              (
                a <_ c
                /\
                (
                  c < d
                  /\
                  (
                    d <_ b
                    /\
                    ( ( c (,) d ) i^i S ) = (/)
                  )
                )
              )
          )
      )
  $.
$}
