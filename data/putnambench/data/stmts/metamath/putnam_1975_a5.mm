$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_a5: positive linearly independent solutions of a second-order
  real differential equation yield a positive constant multiple of their
  geometric mean satisfying the stated nonlinear equation on a closed
  interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P75A5Interval identifies exactly the sets represented by the source
  Interval RR type: the empty interval or a nonempty closed interval with
  ordered real endpoints.

  F, G, and H are total real-valued functions. Continuity of F is expressed
  by membership in the native continuous-function class, while membership of
  G and H in C^2 on RR preserves the source twice-continuously-differentiable
  hypotheses. The entries of ( RR Dn G ) and ( RR Dn H ) are their iterated
  real derivatives.

  The function occurring in the conclusion is written inline as the map
  t |-> c * sqrt(G(t) * H(t)), so the positive constant c remains internally
  existential. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

$c P75A5Interval $.

p75a5-interval-syntax $a wff ( P75A5Interval I ) $.

${
  $d I a b $.

  p75a5-interval-definition $a |- (
    ( P75A5Interval I )
    <->
    (
      I = (/)
      \/
      E. a e. RR E. b e. RR
        ( a <_ b /\ I = ( a [,] b ) )
    )
  ) $.
$}

${
  $d I F G H a b c t x $.

  putnambench-putnam-1975-a5 $a |-
    A. I e. ~P RR
    A. F e. ( RR ^m RR )
    A. G e. ( RR ^m RR )
    A. H e. ( RR ^m RR )
      (
        (
          ( P75A5Interval I )
          /\
          (
            F e. ( RR -cn-> RR )
            /\
            (
              G e. ( ( C^n ` RR ) ` 2 )
              /\
              H e. ( ( C^n ` RR ) ` 2 )
            )
          )
          /\
          (
            A. x e. RR
              ( ( ( RR Dn G ) ` 2 ) ` x )
              =
              ( ( F ` x ) x. ( G ` x ) )
            /\
            A. x e. RR
              ( ( ( RR Dn H ) ` 2 ) ` x )
              =
              ( ( F ` x ) x. ( H ` x ) )
          )
          /\
          (
            A. a e. RR A. b e. RR
              (
                A. x e. RR
                  (
                    ( ( a x. ( G ` x ) ) + ( b x. ( H ` x ) ) )
                    =
                    0
                  )
                ->
                ( a = 0 /\ b = 0 )
              )
            /\
            A. x e. I
              ( 0 < ( G ` x ) /\ 0 < ( H ` x ) )
          )
        )
        ->
        E. c e. RR
          (
            0 < c
            /\
            A. x e. I
              (
                (
                  (
                    (
                      RR
                      Dn
                      (
                        t e. RR |->
                          (
                            c
                            x.
                            ( sqrt ` ( ( G ` t ) x. ( H ` t ) ) )
                          )
                      )
                    )
                    ` 2
                  )
                  ` x
                )
                +
                (
                  1
                  /
                  (
                    (
                      c
                      x.
                      ( sqrt ` ( ( G ` x ) x. ( H ` x ) ) )
                    )
                    ^ 3
                  )
                )
              )
              =
              (
                ( F ` x )
                x.
                (
                  c
                  x.
                  ( sqrt ` ( ( G ` x ) x. ( H ` x ) ) )
                )
              )
          )
      )
  $.
$}
