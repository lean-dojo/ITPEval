$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a4: a real-coefficient polynomial in three variables satisfying
  the specified scaling identity and evaluations determines the distance
  between two of three complex inputs. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 3o is the three-element variable-index set. Thus
  ( 3o mPoly CCfld ) is set.mm's ring of arbitrary finite-support
  polynomials in three variables over the complex field, and
  ( 3o eval CCfld ) evaluates such a polynomial at a complex assignment.
  A polynomial in this ring is its coefficient function on exponent maps;
  requiring every coefficient to belong to RR is exactly the source
  real-coefficient condition. Since 3o is finite, every map in
  ( NN0 ^m 3o ) is a valid finite-support exponent map.

  f remains an arbitrary curried total function from RR x RR to RR. The
  coordinate maps send 0, 1, and 2 to the displayed first, second, and third
  arguments, so all evaluations and the universal scaling identity retain
  their source order. Complex modulus is set.mm's abs, and the conclusion
  inlines the annotated source solution (5 / 3) * sqrt(30).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c e f i p u x y z $.

  putnambench-putnam-1987-a4 $a |-
    A. p e. ( Base ` ( 3o mPoly CCfld ) )
      A. f e. ( ( RR ^m RR ) ^m RR )
        A. a e. CC A. b e. CC A. c e. CC
          (
            (
              A. e e. ( NN0 ^m 3o )
                ( p ` e ) e. RR
              /\
              A. x e. RR A. y e. RR A. z e. RR A. u e. RR
                (
                  (
                    ( ( 3o eval CCfld ) ` p )
                    `
                    (
                      i e. 3o |->
                        if (
                          i = (/) ,
                          ( u x. x ) ,
                          if ( i = 1o , ( u x. y ) , ( u x. z ) )
                        )
                    )
                  )
                  =
                  (
                    ( u ^ 2 )
                    x.
                    ( ( f ` ( y - x ) ) ` ( z - x ) )
                  )
                )
              /\
              (
                ( ( 3o eval CCfld ) ` p )
                `
                (
                  i e. 3o |->
                    if ( i = (/) , 1 , if ( i = 1o , 0 , 0 ) )
                )
              )
              =
              4
              /\
              (
                ( ( 3o eval CCfld ) ` p )
                `
                (
                  i e. 3o |->
                    if ( i = (/) , 0 , if ( i = 1o , 1 , 0 ) )
                )
              )
              =
              5
              /\
              (
                ( ( 3o eval CCfld ) ` p )
                `
                (
                  i e. 3o |->
                    if ( i = (/) , 0 , if ( i = 1o , 0 , 1 ) )
                )
              )
              =
              6
              /\
              (
                ( ( 3o eval CCfld ) ` p )
                `
                (
                  i e. 3o |->
                    if ( i = (/) , a , if ( i = 1o , b , c ) )
                )
              )
              =
              0
              /\
              ( abs ` ( b - a ) ) = ( 5 + 5 )
            )
            ->
            (
              ( abs ` ( c - a ) )
              =
              ( ( 5 / 3 ) x. ( sqrt ` ( 5 x. 6 ) ) )
            )
          )
  $.
$}
