$(
  Statement-only formalization of "The Fundamental Theorem of Integral Calculus" from Hundred
  Theorems item 015. It states the scalar real endpoint-difference theorem for
  a derivative and the Henstock-Kurzweil integral on a closed interval. This
  file contains no proof.
$)

$[ library/set.mm $]

$(
  F and G are total real functions. The restricted universal says that G(x)
  is a derivative of F at x within the closed interval [A,B], including the
  one-sided endpoint interpretation supplied by the interval subspace.

  HT015HKInt is defined by the gauge criterion. For every positive error
  tolerance there is a positive gauge on [A,B] such that every subordinate
  finite tagged partition has its Riemann sum within that tolerance of the
  asserted value. Thus the predicate includes both gauge integrability and
  the value of the integral, without an absolute-integrability assumption.
$)

$c HT015HKInt $.

ht015-hkint-syntax $a wff ( HT015HKInt F A B C ) $.

${
  $d e d n p t k A $.
  $d e d n p t k B $.
  $d e d n p t k C $.
  $d e d n p t k F $.

  ht015-hkint-definition $a |- (
    ( HT015HKInt F A B C )
    <->
    A. e e. RR
      (
        0 < e
        ->
        E. d
          (
            d : ( A [,] B ) --> RR+
            /\
            A. n e. NN0 A. p A. t
              (
                (
                  (
                    (
                      p : ( 0 ... n ) --> RR
                      /\
                      t : ( 0 ..^ n ) --> RR
                    )
                    /\
                    ( ( p ` 0 ) = A /\ ( p ` n ) = B )
                  )
                  /\
                  A. k e. ( 0 ..^ n )
                    (
                      ( p ` k ) < ( p ` ( k + 1 ) )
                      /\
                      (
                        ( t ` k ) e.
                          ( ( p ` k ) [,] ( p ` ( k + 1 ) ) )
                        /\
                        (
                          ( ( t ` k ) - ( d ` ( t ` k ) ) ) <
                            ( p ` k )
                          /\
                          ( p ` ( k + 1 ) ) <
                            ( ( t ` k ) + ( d ` ( t ` k ) ) )
                        )
                      )
                    )
                )
                ->
                (
                  abs `
                    (
                      (
                        sum_ k e. ( 0 ..^ n )
                          (
                            ( F ` ( t ` k ) )
                            x.
                            ( ( p ` ( k + 1 ) ) - ( p ` k ) )
                          )
                      )
                      -
                      C
                    )
                )
                <
                e
              )
          )
      )
  ) $.
$}

${
  $d x A $.
  $d x B $.
  $d x F $.
  $d x G $.

  fundamental-theorem-of-integral-calculus $a |- (
    (
      (
        ( A e. RR /\ B e. RR )
        /\
        ( A <_ B /\ ( F : RR --> RR /\ G : RR --> RR ) )
      )
      /\
      A. x e. ( A [,] B )
        x ( ( A [,] B ) _D ( F |` ( A [,] B ) ) ) ( G ` x )
    )
    ->
    ( HT015HKInt G A B ( ( F ` B ) - ( F ` A ) ) )
  ) $.
$}
