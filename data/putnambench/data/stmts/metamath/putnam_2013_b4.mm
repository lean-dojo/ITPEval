$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_b4: the variance of the product of two continuous real-valued
  functions on the unit interval is bounded using their variances and maximum
  absolute values. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class ( ( 0 [,] 1 ) -cn-> RR ) is set.mm's space of continuous
  real-valued functions on the closed unit interval. U, V, and M range over
  real-valued functionals on that entire space. The antecedent gives exactly
  the source definitions of the integral mean U, variance V, and maximum
  absolute value M; the latter is expanded as attainment together with a
  universal upper bound.

  The S. binders are real Lebesgue integrals over [0,1], agreeing with the
  interval integrals in the ground-truth sources. The map in the conclusion
  is the pointwise product of F and G. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d F G M U V x $.

  putnambench-putnam-2013-b4 $a |-
    A. U e.
      ( RR ^m ( ( 0 [,] 1 ) -cn-> RR ) )
    A. V e.
      ( RR ^m ( ( 0 [,] 1 ) -cn-> RR ) )
    A. M e.
      ( RR ^m ( ( 0 [,] 1 ) -cn-> RR ) )
      (
        (
          (
            A. F e. ( ( 0 [,] 1 ) -cn-> RR )
              ( U ` F )
              =
              (
                S. ( 0 [,] 1 )
                  ( F ` x )
                  _d x
              )
            /\
            A. F e. ( ( 0 [,] 1 ) -cn-> RR )
              ( V ` F )
              =
              (
                S. ( 0 [,] 1 )
                  (
                    (
                      ( F ` x )
                      -
                      ( U ` F )
                    )
                    ^ 2
                  )
                  _d x
              )
          )
          /\
          A. F e. ( ( 0 [,] 1 ) -cn-> RR )
            (
              E. x e. ( 0 [,] 1 )
                ( abs ` ( F ` x ) ) = ( M ` F )
              /\
              A. x e. ( 0 [,] 1 )
                ( abs ` ( F ` x ) ) <_ ( M ` F )
            )
        )
        ->
        A. F e. ( ( 0 [,] 1 ) -cn-> RR )
        A. G e. ( ( 0 [,] 1 ) -cn-> RR )
          (
            V
            `
            (
              x e. ( 0 [,] 1 ) |->
                (
                  ( F ` x )
                  x.
                  ( G ` x )
                )
            )
          )
          <_
          (
            (
              (
                2
                x.
                ( V ` F )
              )
              x.
              ( ( M ` G ) ^ 2 )
            )
            +
            (
              (
                2
                x.
                ( V ` G )
              )
              x.
              ( ( M ` F ) ^ 2 )
            )
          )
      )
  $.
$}
