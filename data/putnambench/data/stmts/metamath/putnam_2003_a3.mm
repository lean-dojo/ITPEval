$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a3: the minimum over real x of the absolute value of the sum of
  sin(x), cos(x), tan(x), cot(x), sec(x), and csc(x) is
  2 * sqrt(2) - 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P03A3Inv0 is the totalized real reciprocal used by the Lean and Rocq
  sources: it is zero at zero and the ordinary reciprocal elsewhere.
  Accordingly, tangent is expanded as sin(x) times P03A3Inv0(cos(x)); this
  preserves the source values at every real x, including zeros of sine or
  cosine, despite set.mm's partial ordinary division and tangent.

  The antecedent is the source pointwise definition of F. The conclusion
  expands IsLeast of its range into attainment of 2 * sqrt(2) - 1 and the
  corresponding lower bound for every real input. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

$c P03A3Inv0 $.

p03a3-total-reciprocal-syntax $a class P03A3Inv0 $.

${
  p03a3-total-reciprocal-definition $a |- P03A3Inv0 =
    ( z e. RR |-> if ( z = 0 , 0 , ( 1 / z ) ) )
  $.
$}

${
  $d F x $.

  putnambench-putnam-2003-a3 $a |-
    A. F e. ( RR ^m RR )
      (
        A. x e. RR
          ( F ` x )
          =
          (
            abs
            `
            (
              (
                (
                  (
                    (
                      ( sin ` x )
                      +
                      ( cos ` x )
                    )
                    +
                    (
                      ( sin ` x )
                      x.
                      ( P03A3Inv0 ` ( cos ` x ) )
                    )
                  )
                  +
                  (
                    P03A3Inv0
                    `
                    (
                      ( sin ` x )
                      x.
                      ( P03A3Inv0 ` ( cos ` x ) )
                    )
                  )
                )
                +
                ( P03A3Inv0 ` ( cos ` x ) )
              )
              +
              ( P03A3Inv0 ` ( sin ` x ) )
            )
          )
        ->
        (
          E. x e. RR
            ( F ` x ) = ( ( 2 x. ( sqrt ` 2 ) ) - 1 )
          /\
          A. x e. RR
            ( ( 2 x. ( sqrt ` 2 ) ) - 1 ) <_ ( F ` x )
        )
      )
  $.
$}
