$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_a4: a class of 2N students whose quiz scores cover every
  integer from 0 through 10 and average exactly 7.4 can be partitioned into
  two N-student groups, each with average 7.4. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite ordinal 0 ..^ (2 x. N) is the full carrier of the 2N students.
  The function space (0 ... ; 1 0) ^m (0 ..^ (2 x. N)) therefore represents
  every score assignment with exactly the source domain and score range.
  Surjectivity states that each possible score occurs at least once.

  The witness s is internally existential, is a subset of the full student
  carrier, and has cardinality N. Its relative complement in the carrier is
  the second group. Both sums and both exact rational averages are stated
  explicitly. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d N f i k s $.

  putnambench-putnam-2017-a4 $a |- A. N e. NN0
    A. f e. ( ( 0 ... ; 1 0 ) ^m ( 0 ..^ ( 2 x. N ) ) )
      (
        (
          A. k e. ( 0 ... ; 1 0 )
            E. i e. ( 0 ..^ ( 2 x. N ) )
              ( f ` i ) = k
          /\
          (
            (
              sum_ i e. ( 0 ..^ ( 2 x. N ) )
                ( f ` i )
            )
            /
            ( 2 x. N )
          )
          =
          ( ; 7 4 / ; 1 0 )
        )
        ->
        E. s
          (
            (
              s C_ ( 0 ..^ ( 2 x. N ) )
              /\
              ( # ` s ) = N
            )
            /\
            (
              (
                (
                  sum_ i e. s
                    ( f ` i )
                )
                /
                N
              )
              =
              ( ; 7 4 / ; 1 0 )
              /\
              (
                (
                  sum_ i e.
                    ( ( 0 ..^ ( 2 x. N ) ) \ s )
                    ( f ` i )
                )
                /
                N
              )
              =
              ( ; 7 4 / ; 1 0 )
            )
          )
      )
  $.
$}
