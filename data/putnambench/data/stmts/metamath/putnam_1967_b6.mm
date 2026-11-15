$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b6: a bounded real function with both partial derivatives in
  the open unit disk has an interior point where the sum of the squared
  partial derivatives is at most 16. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F is an arbitrary curried total function from RR x RR to RR. The first
  antecedent requires both coordinate slices to be differentiable at each
  point of the open unit disk. The second is the source bound on the closed
  unit disk. The conclusion keeps both point coordinates existential and
  evaluates the native set.mm real derivative on the corresponding slices.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F t x y $.

  putnambench-putnam-1967-b6 $a |-
    A. F e. ( ( RR ^m RR ) ^m RR )
      (
        (
          (
            A. x e. RR A. y e. RR
              (
                ( ( x ^ 2 ) + ( y ^ 2 ) ) < 1
                ->
                (
                  x e.
                    dom
                      (
                        RR _D
                          ( t e. RR |-> ( ( F ` t ) ` y ) )
                      )
                  /\
                  y e.
                    dom
                      (
                        RR _D
                          ( t e. RR |-> ( ( F ` x ) ` t ) )
                      )
                )
              )
          )
          /\
          A. x e. RR A. y e. RR
            (
              ( ( x ^ 2 ) + ( y ^ 2 ) ) <_ 1
              ->
              ( abs ` ( ( F ` x ) ` y ) ) <_ 1
            )
        )
        ->
        E. x e. RR E. y e. RR
          (
            ( ( x ^ 2 ) + ( y ^ 2 ) ) < 1
            /\
            (
              (
                (
                  (
                    RR _D
                      ( t e. RR |-> ( ( F ` t ) ` y ) )
                  )
                  ` x
                )
                ^ 2
              )
              +
              (
                (
                  (
                    RR _D
                      ( t e. RR |-> ( ( F ` x ) ` t ) )
                  )
                  ` y
                )
                ^ 2
              )
            )
            <_
            ( 8 + 8 )
          )
      )
  $.
$}
