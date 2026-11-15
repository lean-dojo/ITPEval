$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b2: the one-eighth bound for initial integrals of a
  continuously differentiable real function with zero integral on the unit
  interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. Membership of its
  restriction to [0,1] in the order-one C^n class is set.mm's native
  formulation of continuous differentiability on that closed interval.
  The relative derivative sequence supplies the first derivative at every
  point of the interval, including its endpoints.

  M is characterized as the attained maximum of the absolute first
  derivative by an existential equality and a universal upper bound. The
  S. binder is the real Lebesgue integral; using closed intervals agrees
  with the source interval integrals because endpoints have measure zero.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F M a x $.

  putnambench-putnam-2007-b2 $a |-
    A. F e. ( RR ^m RR )
      A. M e. RR
        (
          (
            (
              (
                ( F |` ( 0 [,] 1 ) )
                e. ( ( C^n ` ( 0 [,] 1 ) ) ` 1 )
                /\
                S. ( 0 [,] 1 ) ( F ` x ) _d x = 0
              )
              /\
              E. x e. ( 0 [,] 1 )
                (
                  abs
                  `
                  (
                    (
                      (
                        ( 0 [,] 1 )
                        Dn
                        ( F |` ( 0 [,] 1 ) )
                      )
                      ` 1
                    )
                    ` x
                  )
                )
                =
                M
            )
            /\
            A. x e. ( 0 [,] 1 )
              (
                abs
                `
                (
                  (
                    (
                      ( 0 [,] 1 )
                      Dn
                      ( F |` ( 0 [,] 1 ) )
                    )
                    ` 1
                  )
                  ` x
                )
              )
              <_
              M
          )
          ->
          A. a e. ( 0 (,) 1 )
            (
              abs
              `
              (
                S. ( 0 [,] a ) ( F ` x ) _d x
              )
            )
            <_
            (
              ( 1 / 8 )
              x.
              M
            )
        )
    $.
$}
