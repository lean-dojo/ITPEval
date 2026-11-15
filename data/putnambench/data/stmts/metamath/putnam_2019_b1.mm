$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b1: for each nonnegative integer n, the number of four-point
  subsets of the integer points at the origin or on a circle of squared
  radius 2^k for some 0 <= k <= n that form a square is 5n + 1. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P19B1Plane is the full integer coordinate plane. P19B1Pn(n) is the source
  set P_n, with the exponent k still internally existentially quantified
  over the inclusive interval from zero through n. P19B1DistSq is squared
  Euclidean distance on that plane.

  P19B1Square(S) says that S consists of four distinct points A, B, C, D in
  cyclic order, with positive equal squared side lengths and equal squared
  diagonal lengths. Squaring preserves equality and positivity of the
  Euclidean distances, so this is equivalent to the source square predicate.
  The definitions and final declaration are unproved $a statement encodings;
  this database contains no $p proof declaration.
$)

$c P19B1Plane P19B1Pn P19B1DistSq P19B1Square $.

p19b1-plane-syntax $a class P19B1Plane $.
p19b1-pn-syntax $a class ( P19B1Pn n ) $.
p19b1-distance-square-syntax $a class ( P19B1DistSq A B ) $.
p19b1-square-syntax $a wff ( P19B1Square S ) $.

p19b1-plane-definition $a |- P19B1Plane = ( ZZ X. ZZ ) $.

${
  $d k n p $.

  p19b1-pn-definition $a |- ( P19B1Pn n ) = {
    p e. P19B1Plane |
      (
        p = <. 0 , 0 >.
        \/
        E. k e. ( 0 ... n )
          (
            (
              ( ( 1st ` p ) ^ 2 )
              +
              ( ( 2nd ` p ) ^ 2 )
            )
            =
            ( 2 ^ k )
          )
      )
  } $.
$}

p19b1-distance-square-definition $a |- (
  P19B1DistSq A B
) = (
  (
    ( ( 1st ` A ) - ( 1st ` B ) ) ^ 2
  )
  +
  (
    ( ( 2nd ` A ) - ( 2nd ` B ) ) ^ 2
  )
) $.

${
  $d A B C D S p $.

  p19b1-square-definition $a |- (
    ( P19B1Square S )
    <->
    (
      (
        S e. Fin
        /\
        S C_ P19B1Plane
      )
      /\
      E. A e. P19B1Plane
        E. B e. P19B1Plane
          E. C e. P19B1Plane
            E. D e. P19B1Plane
              (
                S = {
                  p e. P19B1Plane |
                    (
                      (
                        (
                          p = A
                          \/
                          p = B
                        )
                        \/
                        p = C
                      )
                      \/
                      p = D
                    )
                }
                /\
                (
                  ( # ` S ) = 4
                  /\
                  (
                    0 < ( P19B1DistSq A B )
                    /\
                    (
                      ( P19B1DistSq A B ) = ( P19B1DistSq B C )
                      /\
                      (
                        ( P19B1DistSq B C ) = ( P19B1DistSq C D )
                        /\
                        (
                          ( P19B1DistSq C D ) = ( P19B1DistSq D A )
                          /\
                          ( P19B1DistSq A C ) = ( P19B1DistSq B D )
                        )
                      )
                    )
                  )
                )
              )
    )
  ) $.
$}

${
  $d S n $.

  putnambench-putnam-2019-b1 $a |- A. n e. NN0
    (
      #
      `
      {
        S e. Fin |
          (
            S C_ ( P19B1Pn n )
            /\
            ( P19B1Square S )
          )
      }
    )
    =
    ( ( 5 x. n ) + 1 )
  $.
$}
