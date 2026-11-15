$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_a1: the real parameters for which the two transposed
  quadratic curves have a common point with tangent slopes whose product
  is one are exactly four explicit values. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source predicate P is inlined using its defining biconditional.
  For the displayed polynomial f(t) = a*t^2 + a*t + 1/24, its everywhere
  defined real derivative is 2*a*t + a, so the derivative-product condition
  is written explicitly. The witnesses x and y remain existentially
  quantified over all real numbers.

  Membership in the source solution set is expanded as equality with one of
  2/3, 3/2, (13 + sqrt(601))/12, and (13 - sqrt(601))/12. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d a x y $.

  putnambench-putnam-2007-a1 $a |- A. a e. RR
    (
      (
        E. x e. RR E. y e. RR
          (
            (
              (
                (
                  ( a x. ( x ^ 2 ) )
                  +
                  ( a x. x )
                )
                +
                ( 1 / ; 2 4 )
              )
              =
              y
              /\
              (
                (
                  ( a x. ( y ^ 2 ) )
                  +
                  ( a x. y )
                )
                +
                ( 1 / ; 2 4 )
              )
              =
              x
            )
            /\
            (
              (
                ( ( 2 x. a ) x. x )
                +
                a
              )
              x.
              (
                ( ( 2 x. a ) x. y )
                +
                a
              )
            )
            =
            1
          )
      )
      <->
      (
        a = ( 2 / 3 )
        \/
        (
          a = ( 3 / 2 )
          \/
          (
            a
            =
            (
              (
                ; 1 3
                +
                ( sqrt ` ; ; 6 0 1 )
              )
              /
              ; 1 2
            )
            \/
            a
            =
            (
              (
                ; 1 3
                -
                ( sqrt ` ; ; 6 0 1 )
              )
              /
              ; 1 2
            )
          )
        )
      )
    )
  $.
$}
