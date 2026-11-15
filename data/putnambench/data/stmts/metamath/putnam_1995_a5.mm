$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a5: every positive-dimensional family of differentiable real
  functions satisfying a constant linear ODE system with strictly positive
  coefficients and tending to zero at positive infinity is linearly
  dependent. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal interval 0 ..^ n is the n-element carrier representing Fin n.
  Thus x ranges over arbitrary n-indexed families of total real functions,
  and a ranges over arbitrary n by n real coefficient families. Containment
  of RR in each derivative domain expresses differentiability at every real
  point, and the displayed finite sum is the source ODE system.

  The epsilon-threshold clause is convergence of every x_i(t) to zero as the
  real variable t tends to positive infinity. The conclusion is exactly the
  negation of linear independence: it negates the assertion that every real
  coefficient family whose pointwise linear combination is zero has all
  coefficients zero. The source solution is True, so its biconditional with
  this universal property is equivalent to the property asserted below. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d M a b e i j n t x $.

  putnambench-putnam-1995-a5 $a |- A. n e. NN
    A. x e. ( ( RR ^m RR ) ^m ( 0 ..^ n ) )
    A. a e.
      (
        ( RR ^m ( 0 ..^ n ) )
        ^m
        ( 0 ..^ n )
      )
      (
        (
          A. i e. ( 0 ..^ n )
            RR C_ dom ( RR _D ( x ` i ) )
          /\
          (
            A. i e. ( 0 ..^ n )
              A. j e. ( 0 ..^ n )
                0 < ( ( a ` i ) ` j )
            /\
            (
              A. t e. RR
                A. i e. ( 0 ..^ n )
                  (
                    ( ( RR _D ( x ` i ) ) ` t )
                    =
                    (
                      sum_ j e. ( 0 ..^ n )
                        (
                          ( ( a ` i ) ` j )
                          x.
                          ( ( x ` j ) ` t )
                        )
                    )
                  )
              /\
              A. i e. ( 0 ..^ n )
                A. e e. RR
                  (
                    0 < e
                    ->
                    E. M e. RR
                      A. t e. RR
                        (
                          M <_ t
                          ->
                          ( abs ` ( ( x ` i ) ` t ) ) < e
                        )
                  )
            )
          )
        )
        ->
        -.
        A. b e. ( RR ^m ( 0 ..^ n ) )
          (
            A. t e. RR
              (
                sum_ i e. ( 0 ..^ n )
                  (
                    ( b ` i )
                    x.
                    ( ( x ` i ) ` t )
                  )
              )
              =
              0
            ->
            A. i e. ( 0 ..^ n ) ( b ` i ) = 0
          )
      )
  $.
$}
