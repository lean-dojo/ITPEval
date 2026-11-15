$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a1: every nonzero Taylor coefficient at zero of
  (1 - x + x^2) exp(x) is rational with reduced numerator equal to one
  or a prime. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR and RR ^m NN0 retain the source's total real function and
  real-valued coefficient sequence. The all-orders C^n condition is the
  global smoothness assumption from Lean and the derivative-existence
  assumption from Rocq.

  P14A1Deriv totalizes set.mm's partial real derivative by assigning zero
  outside its domain. Under the smoothness premise this agrees everywhere
  with the ordinary derivative, and IterComp includes derivative order zero.
  Thus the displayed quotient by n factorial is the source Taylor
  coefficient at zero.

  The internally existential rational q is identified with the coefficient.
  Set.mm's numer is the integer numerator of q in its unique reduced
  representation with positive denominator, and Prime is its class of
  positive natural primes. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

$c P14A1Deriv P14A1IterDeriv $.

p14a1-deriv-syntax $a class P14A1Deriv $.
p14a1-iter-deriv-syntax $a class ( P14A1IterDeriv n A ) $.

${
  $d A x $.

  p14a1-deriv-definition $a |- P14A1Deriv =
    (
      A e. ( RR ^m RR ) |->
        (
          x e. RR |->
            if (
              x e. dom ( RR _D A ) ,
              ( ( RR _D A ) ` x ) ,
              0
            )
        )
    ) $.
$}

p14a1-iter-deriv-definition $a |- ( P14A1IterDeriv n A ) =
  (
    ( ( IterComp ` P14A1Deriv ) ` n )
    `
    A
  ) $.

${
  $d c f k n q x $.

  putnambench-putnam-2014-a1 $a |-
    A. f e. ( RR ^m RR )
    A. c e. ( RR ^m NN0 )
      (
        (
          (
            A. x e. RR
              ( f ` x )
              =
              (
                (
                  ( 1 - x )
                  +
                  ( x ^ 2 )
                )
                x.
                ( exp ` x )
              )
            /\
            A. n e. NN0
              f e. ( ( C^n ` RR ) ` n )
          )
          /\
          A. n e. NN0
            ( c ` n )
            =
            (
              (
                ( P14A1IterDeriv n f )
                `
                0
              )
              /
              ( ! ` n )
            )
        )
        ->
        A. k e. NN0
          (
            ( c ` k ) =/= 0
            ->
            E. q e. QQ
              (
                ( c ` k ) = q
                /\
                (
                  ( numer ` q ) = 1
                  \/
                  ( numer ` q ) e. Prime
                )
              )
          )
      )
  $.
$}
