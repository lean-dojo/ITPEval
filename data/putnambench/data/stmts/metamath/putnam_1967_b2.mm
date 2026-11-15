$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b2: coefficients in two real quadratic identities determined
  by parameters in the closed unit interval have the stated four-ninths
  lower bounds on their maxima. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The set.mm conditional if ( u <_ v , v , u ) is the maximum of the two
  real numbers u and v, so the two nested conditionals below are exactly the
  source maxima max(max(A,B),C) and max(max(alpha,beta),gamma). The source
  coefficients alpha, beta, and gamma are named a, b, and c here. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A B C a b c p r x y $.

  putnambench-putnam-1967-b2 $a |- A. p e. RR A. r e. RR
    A. A e. RR A. B e. RR A. C e. RR
    A. a e. RR A. b e. RR A. c e. RR
      (
        (
          (
            ( 0 <_ p /\ p <_ 1 )
            /\
            ( 0 <_ r /\ r <_ 1 )
          )
          /\
          (
            A. x e. RR A. y e. RR
              (
                ( ( p x. x ) + ( ( 1 - p ) x. y ) ) ^ 2
              )
              =
              (
                (
                  ( A x. ( x ^ 2 ) )
                  +
                  ( ( B x. x ) x. y )
                )
                +
                ( C x. ( y ^ 2 ) )
              )
          )
          /\
          A. x e. RR A. y e. RR
            (
              (
                ( p x. x )
                +
                ( ( 1 - p ) x. y )
              )
              x.
              (
                ( r x. x )
                +
                ( ( 1 - r ) x. y )
              )
            )
            =
            (
              (
                ( a x. ( x ^ 2 ) )
                +
                ( ( b x. x ) x. y )
              )
              +
              ( c x. ( y ^ 2 ) )
            )
        )
        ->
        (
          ( 4 / 9 )
          <_
          if (
            if ( A <_ B , B , A ) <_ C ,
            C ,
            if ( A <_ B , B , A )
          )
          /\
          ( 4 / 9 )
          <_
          if (
            if ( a <_ b , b , a ) <_ c ,
            c ,
            if ( a <_ b , b , a )
          )
        )
      )
  $.
$}
