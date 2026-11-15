$(
  Statement-only formalization of PutnamBench artifact putnam_1963_a3:
  the integral formula for the solution of an iterated Euler differential
  equation with vanishing initial derivatives at one. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the set of total real functions. P is an NN0-indexed family
  of endomorphisms of that function space. The recurrence uses set.mm's
  partial real derivative with value zero outside its domain, matching the
  total derivative convention of the sources.

  The C^n premises state n-fold continuous differentiability on [1,+oo) and
  on a two-sided neighborhood of 1. The integral uses the documented kernel

    (x-t)^(n-1) f(t) / ((n-1)! t^n).

  Since x is at least 1, the Lebesgue integral over [1,x] is the source
  interval integral. The final declaration is the single unproved $a
  statement; this database contains no $p proof statement.
$)

${
  $d e i t x F P Y n $.

  putnambench-putnam-1963-a3 $a |- A. P e.
    ( ( ( RR ^m RR ) ^m ( RR ^m RR ) ) ^m NN0 )
    A. n e. NN
    A. F e. ( RR ^m RR )
    A. Y e. ( RR ^m RR )
      (
        (
          (
            A. Y e. ( RR ^m RR )
              ( ( P ` 0 ) ` Y ) = Y
            /\
            A. i e. NN0 A. Y e. ( RR ^m RR )
              (
                ( ( P ` ( i + 1 ) ) ` Y )
                =
                (
                  ( P ` i )
                  `
                  (
                    x e. RR |->
                      (
                        x
                        x.
                        if (
                          x e. dom ( RR _D Y ) ,
                          ( ( RR _D Y ) ` x ) ,
                          0
                        )
                      )
                      -
                      ( i x. ( Y ` x ) )
                  )
                )
              )
          )
          /\
          (
            (
              (
                F |` { x e. RR | 1 <_ x }
              )
              e.
              (
                ( C^n ` { x e. RR | 1 <_ x } )
                ` 0
              )
              /\
              (
                Y |` { x e. RR | 1 <_ x }
              )
              e.
              (
                ( C^n ` { x e. RR | 1 <_ x } )
                ` n
              )
            )
            /\
            E. e e. RR+
              (
                Y |` ( ( 1 - e ) [,] ( 1 + e ) )
              )
              e.
              (
                (
                  C^n
                  ` ( ( 1 - e ) [,] ( 1 + e ) )
                )
                ` n
              )
          )
        )
        ->
        (
          (
            (
              A. i e. ( 0 ..^ n )
                ( ( ( RR Dn Y ) ` i ) ` 1 ) = 0
              /\
              A. x e. { x e. RR | 1 <_ x }
                ( ( ( P ` n ) ` Y ) ` x ) = ( F ` x )
            )
            <->
            A. x e. { x e. RR | 1 <_ x }
              ( Y ` x )
              =
              S. ( 1 [,] x )
                (
                  (
                    ( ( x - t ) ^ ( n - 1 ) )
                    x.
                    ( F ` t )
                  )
                  /
                  (
                    ( ! ` ( n - 1 ) )
                    x.
                    ( t ^ n )
                  )
                )
                _d t
          )
        )
      )
  $.
$}
