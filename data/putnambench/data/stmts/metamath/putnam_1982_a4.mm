$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_a4: the unique global continuously differentiable real solution
  of y' = -z^3 and z' = y^3 with initial value (1,0) has a common positive
  period. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F, G, Y, and Z range over total real-valued functions on the reals.
  Membership in ( ( C^n ` RR ) ` 1 ) is set.mm's native assertion of global
  continuous differentiability through order one, and
  ( ( RR Dn F ) ` 1 ) is the real derivative of F.

  The antecedent first states the initial conditions and both differential
  equations for F and G. Its negated existential then states uniqueness among
  all total global C^1 real solution pairs with the same initial conditions.
  The conclusion retains the internally existential positive common period
  and requires both periodicity equalities at every real argument. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d F G L x Y Z $.

  putnambench-putnam-1982-a4 $a |-
    A. F e. ( RR ^m RR )
    A. G e. ( RR ^m RR )
      (
        (
          (
            (
              ( F ` 0 ) = 1
              /\
              ( G ` 0 ) = 0
            )
            /\
            (
              F e. ( ( C^n ` RR ) ` 1 )
              /\
              G e. ( ( C^n ` RR ) ` 1 )
            )
          )
          /\
          A. x e. RR
            (
              ( ( ( RR Dn F ) ` 1 ) ` x )
              =
              ( -u ( ( G ` x ) ^ 3 ) )
              /\
              ( ( ( RR Dn G ) ` 1 ) ` x )
              =
              ( ( F ` x ) ^ 3 )
            )
        )
        /\
        -. E. Y e. ( RR ^m RR )
          E. Z e. ( RR ^m RR )
            (
              (
                F =/= Y
                \/
                G =/= Z
              )
              /\
              (
                (
                  (
                    ( Y ` 0 ) = 1
                    /\
                    ( Z ` 0 ) = 0
                  )
                  /\
                  (
                    Y e. ( ( C^n ` RR ) ` 1 )
                    /\
                    Z e. ( ( C^n ` RR ) ` 1 )
                  )
                )
                /\
                A. x e. RR
                  (
                    ( ( ( RR Dn Y ) ` 1 ) ` x )
                    =
                    ( -u ( ( Z ` x ) ^ 3 ) )
                    /\
                    ( ( ( RR Dn Z ) ` 1 ) ` x )
                    =
                    ( ( Y ` x ) ^ 3 )
                  )
              )
            )
      )
      ->
      E. L e. RR
        (
          0 < L
          /\
          A. x e. RR
            (
              ( F ` ( x + L ) ) = ( F ` x )
              /\
              ( G ` ( x + L ) ) = ( G ` x )
            )
        )
      )
  $.
$}
