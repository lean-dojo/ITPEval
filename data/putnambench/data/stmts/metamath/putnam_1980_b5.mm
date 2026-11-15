$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_b5: characterization of the nonnegative real parameters for
  which the specified nonnegative strictly increasing convex continuous
  functions on the unit interval are closed under pointwise multiplication.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P80B5S t F expands membership in the source set S_t. The function F remains
  an arbitrary total function from RR to RR; only its restriction to [0,1] is
  required to be continuous. Nonnegativity, strict monotonicity, convexity,
  and the defining three-point inequality are expanded at their source
  quantifier scopes.

  The pointwise product is the total function x |-> (f(x) * g(x)), and the
  source solution predicate is inlined as t <= 1. The final declaration is
  the single unproved corpus assertion; this database contains no $p proof
  statement.
$)

$c P80B5S $.

p80b5-membership-syntax $a wff ( P80B5S T F ) $.

${
  $d F T s u v x y $.

  p80b5-membership-definition $a |- (
    ( P80B5S T F )
    <->
    (
      F e. ( RR ^m RR )
      /\
      (
        A. x e. ( 0 [,] 1 )
          0 <_ ( F ` x )
        /\
        (
          A. x e. ( 0 [,] 1 )
            A. y e. ( 0 [,] 1 )
              (
                x < y
                ->
                ( F ` x ) < ( F ` y )
              )
          /\
          (
            A. u e. ( 0 [,] 1 )
              A. v e. ( 0 [,] 1 )
                A. s e. ( 0 [,] 1 )
                  (
                    F
                    `
                    (
                      ( s x. u )
                      +
                      ( ( 1 - s ) x. v )
                    )
                  )
                  <_
                  (
                    ( s x. ( F ` u ) )
                    +
                    ( ( 1 - s ) x. ( F ` v ) )
                  )
            /\
            (
              ( F |` ( 0 [,] 1 ) )
              e.
              ( ( 0 [,] 1 ) -cn-> RR )
              /\
              (
                (
                  ( F ` 1 )
                  -
                  ( 2 x. ( F ` ( 2 / 3 ) ) )
                )
                +
                ( F ` ( 1 / 3 ) )
              )
              >_
              (
                T
                x.
                (
                  (
                    ( F ` ( 2 / 3 ) )
                    -
                    ( 2 x. ( F ` ( 1 / 3 ) ) )
                  )
                  +
                  ( F ` 0 )
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
  $d f g t x $.

  putnambench-putnam-1980-b5 $a |- A. t e. RR
    (
      0 <_ t
      ->
      (
        A. f A. g
          (
            (
              ( P80B5S t f )
              /\
              ( P80B5S t g )
            )
            ->
            (
              P80B5S
              t
              (
                x e. RR |->
                  (
                    ( f ` x )
                    x.
                    ( g ` x )
                  )
              )
            )
          )
        <->
        t <_ 1
      )
    )
  $.
$}
