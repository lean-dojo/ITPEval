$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a5:
  the number of orderings of the integers from 1 through n in which every
  entry after the first has an earlier entry differing from it by one is
  2^(n-1). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An ordering is represented as a bijection f from the finite interval
  1 ... n onto itself. For every position m from 2 through n, the internally
  existential position k ranges from 1 through m - 1. The final declaration
  is an unproved $a assertion; this file contains no $p proof statement.
$)

${
  $d f k m n $.

  putnambench-putnam-1965-a5 $a
    |- A. n e. NN
      (
        ( # `
          { f |
            (
              f : ( 1 ... n ) -1-1-onto-> ( 1 ... n )
              /\
              A. m e. ( 2 ... n )
                E. k e. ( 1 ..^ m )
                  (
                    ( f ` m ) = ( ( f ` k ) + 1 )
                    \/
                    ( f ` m ) = ( ( f ` k ) - 1 )
                  )
            )
          }
        )
        =
        ( 2 ^ ( n - 1 ) )
      )
  $.
$}
