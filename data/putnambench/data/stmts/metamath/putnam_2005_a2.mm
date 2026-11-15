$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_a2: the number of unit-step rook tours of the n-by-3 integer
  grid from (1,1) to (n,1). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A tour is represented by a bijection p from 1 ... 3n onto the grid
  (1 ... n) X. (1 ... 3). This is equivalent to the source's total
  natural-indexed function: restrict it to 1 ... 3n, or extend this finite
  function by the ordered pair (0,0) outside that interval.

  The restricted universal condition says that consecutive points share one
  coordinate and differ by one in the other. The endpoint conditions are
  literal. The right side is the explicit solution recorded with the source
  statement. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d i n p $.

  putnambench-putnam-2005-a2 $a |- A. n e. NN
    (
      (
        #
        `
        {
          p e.
            (
              ( ( 1 ... n ) X. ( 1 ... 3 ) )
              ^m
              ( 1 ... ( 3 x. n ) )
            )
          |
          (
            p
            :
            ( 1 ... ( 3 x. n ) )
            -1-1-onto->
            ( ( 1 ... n ) X. ( 1 ... 3 ) )
            /\
            (
              (
                ( p ` 1 ) = <. 1 , 1 >.
                /\
                ( p ` ( 3 x. n ) ) = <. n , 1 >.
              )
              /\
              A. i e. ( 1 ... ( ( 3 x. n ) - 1 ) )
                (
                  (
                    (
                      ( 1st ` ( p ` i ) )
                      =
                      ( 1st ` ( p ` ( i + 1 ) ) )
                      /\
                      (
                        abs
                        `
                        (
                          ( 2nd ` ( p ` ( i + 1 ) ) )
                          -
                          ( 2nd ` ( p ` i ) )
                        )
                      )
                      =
                      1
                    )
                    \/
                    (
                      ( 2nd ` ( p ` i ) )
                      =
                      ( 2nd ` ( p ` ( i + 1 ) ) )
                      /\
                      (
                        abs
                        `
                        (
                          ( 1st ` ( p ` ( i + 1 ) ) )
                          -
                          ( 1st ` ( p ` i ) )
                        )
                      )
                      =
                      1
                    )
                  )
                )
            )
          )
        }
      )
      =
      if
      (
        n = 1 ,
        0 ,
        ( 2 ^ ( n - 2 ) )
      )
    )
  $.
$}
