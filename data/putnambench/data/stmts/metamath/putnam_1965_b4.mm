$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b4:
  the recurrence, exact convergence domain, and square-root limit of the
  ratio of the even and odd binomial-coefficient polynomials. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The families f, u, and v map each nonnegative integer to a total
  real-valued function. The finite sums reproduce the even- and odd-indexed
  binomial polynomials from the sources. Substituting the explicit source
  solution gives p(h)(x) = h(x) + x, q(h)(x) = h(x) + 1, the convergence
  set {x in RR | 0 <= x}, and limit function sqrt.

  The quotient is totalized to zero when its denominator vanishes, matching
  real division in the Lean source. Sequential convergence is expressed by
  set.mm's real-sequence limit relation. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d f i l m n u v x $.

  putnambench-putnam-1965-b4 $a |-
    A. f e. ( ( RR ^m RR ) ^m NN0 )
    A. u e. ( ( RR ^m RR ) ^m NN0 )
    A. v e. ( ( RR ^m RR ) ^m NN0 )
      (
        (
          (
            A. n e. NN A. x e. RR
              ( ( u ` n ) ` x )
              =
              (
                sum_ i e. ( 0 ... ( |_ ` ( n / 2 ) ) )
                  (
                    ( n _C ( 2 x. i ) )
                    x.
                    ( x ^ i )
                  )
              )
            /\
            A. n e. NN A. x e. RR
              ( ( v ` n ) ` x )
              =
              (
                sum_ i e.
                  ( 0 ... ( |_ ` ( ( n - 1 ) / 2 ) ) )
                  (
                    ( n _C ( ( 2 x. i ) + 1 ) )
                    x.
                    ( x ^ i )
                  )
              )
          )
          /\
          A. n e. NN A. x e. RR
            (
              (
                ( ( v ` n ) ` x ) = 0
                ->
                ( ( f ` n ) ` x ) = 0
              )
              /\
              (
                ( ( v ` n ) ` x ) =/= 0
                ->
                ( ( f ` n ) ` x )
                =
                (
                  ( ( u ` n ) ` x )
                  /
                  ( ( v ` n ) ` x )
                )
              )
            )
        )
        ->
        (
          A. n e. NN A. x e. RR
            (
              ( ( v ` n ) ` x ) =/= 0
              ->
              (
                ( ( v ` ( n + 1 ) ) ` x ) =/= 0
                ->
                (
                  ( ( ( f ` n ) ` x ) + 1 ) =/= 0
                  ->
                  ( ( f ` ( n + 1 ) ) ` x )
                  =
                  (
                    ( ( ( f ` n ) ` x ) + x )
                    /
                    ( ( ( f ` n ) ` x ) + 1 )
                  )
                )
              )
            )
          /\
          (
            { x e. RR | 0 <_ x }
            =
            {
              x e. RR |
              E. l e. RR
                (
                  m e. NN0 |->
                    ( ( f ` m ) ` x )
                )
                ~~>
                l
            }
            /\
            A. x e. { x e. RR | 0 <_ x }
              (
                m e. NN0 |->
                  ( ( f ` m ) ` x )
              )
              ~~>
              ( sqrt ` x )
          )
        )
      )
  $.
$}
