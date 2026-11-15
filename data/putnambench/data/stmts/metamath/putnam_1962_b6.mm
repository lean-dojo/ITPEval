$(
  Statement-only formalization of PutnamBench artifact putnam_1962_b6:
  a bounded real trigonometric polynomial attaining absolute value one at
  2n points is, when nonconstant, a phase shift of cos(nx). This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The coefficient functions A and B are arbitrary real sequences indexed by
  nonnegative integers, F is the resulting real trigonometric polynomial,
  and S is a subset of the half-open interval [0,2*pi) with cardinality 2*n.
  The final declaration is an unproved $a statement.
$)

${
  $d A B F S c k n x $.

  putnambench-putnam-1962-b6 $a |- A. n e. NN0
    A. A A. B A. S A. F
      (
        (
          (
            (
              A : NN0 --> RR
              /\
              B : NN0 --> RR
            )
            /\
            (
              F : RR --> RR
              /\
              F =
                (
                  x e. RR |->
                    sum_ k e. ( 0 ... n )
                      (
                        (
                          ( A ` k )
                          x.
                          ( sin ` ( k x. x ) )
                        )
                        +
                        (
                          ( B ` k )
                          x.
                          ( cos ` ( k x. x ) )
                        )
                      )
                )
            )
          )
          /\
          (
            A. x e. ( 0 [,] ( 2 x. _pi ) )
              ( abs ` ( F ` x ) ) <_ 1
            /\
            (
              (
                ( # ` S ) = ( 2 x. n )
                /\
                S C_ ( 0 [,) ( 2 x. _pi ) )
              )
              /\
              A. x e. S
                ( abs ` ( F ` x ) ) = 1
            )
          )
        )
        ->
        (
          (
            -. E. c e. RR
              F = ( x e. RR |-> c )
          )
          ->
          E. c e. RR
            F =
              (
                x e. RR |->
                  ( cos ` ( ( n x. x ) + c ) )
              )
        )
      )
  $.
$}
