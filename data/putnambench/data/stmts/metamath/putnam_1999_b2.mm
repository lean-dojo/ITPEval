$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_b2: a complex polynomial P satisfying P(x) = Q(x) P''(x)
  for a quadratic complex polynomial Q has degree(P) distinct complex roots
  whenever P has two distinct complex roots. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly ` CC is SetMM's set of complex polynomial functions, deg is their
  natural-valued polynomial degree (including the zero-polynomial convention),
  and ( ( CC Dn P ) ` 2 ) is the second complex derivative of P.

  The final existential set S has exactly deg(P) elements and consists only
  of roots of P. This is equivalent to the injective Fin-indexed family and
  duplicate-free sequence formulations in the other corpus languages.
  The declaration below is an unproved $a statement; there is no $p proof
  declaration in this file.
$)

${
  $d P Q S x y z $.

  putnambench-putnam-1999-b2 $a |-
    A. P e. ( Poly ` CC )
      A. Q e. ( Poly ` CC )
        (
          (
            ( deg ` Q ) = 2
            /\
            A. z e. CC
              ( P ` z )
              =
              (
                ( Q ` z )
                x.
                ( ( ( CC Dn P ) ` 2 ) ` z )
              )
          )
          ->
          (
            (
              E. x e. CC
                E. y e. CC
                  (
                    x =/= y
                    /\
                    (
                      ( P ` x ) = 0
                      /\
                      ( P ` y ) = 0
                    )
                  )
            )
            ->
            E. S e. ~P CC
              (
                ( # ` S ) = ( deg ` P )
                /\
                A. z e. S ( P ` z ) = 0
              )
          )
        )
  $.
$}
