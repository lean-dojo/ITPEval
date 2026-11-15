$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b6: parity of the intersection of a half-system of nonzero
  elements in a field of odd prime-square order with its doubles. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over SetMM field structures, Base ` F is the field carrier, and
  +g, -g, and 0g are its addition, subtraction, and zero. The hypotheses
  preserve the finite carrier of cardinality p^2, the subset S of nonzero
  elements, and its exact cardinality (p^2 - 1) / 2.

  For each nonzero carrier element a, negating the biconditional says exactly
  one of a and -a belongs to S. The restricted class in the conclusion is the
  source set of doubles a + a with a in S, and remainder zero modulo two is
  equivalent to even finite cardinality. Since p is odd, the displayed
  natural-number quotient agrees with the integer and real presentations in
  the ground-truth sources. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d F S a p x $.

  putnambench-putnam-1987-b6 $a |-
    A. p e. NN0 A. F A. S
      (
        (
          (
            (
              (
                p e. Prime
                /\
                ( p mod 2 ) = 1
              )
              /\
              (
                F e. Field
                /\
                (
                  ( Base ` F ) e. Fin
                  /\
                  ( # ` ( Base ` F ) ) = ( p ^ 2 )
                )
              )
            )
            /\
            (
              S C_ ( Base ` F )
              /\
              (
                A. x e. S x =/= ( 0g ` F )
                /\
                ( # ` S ) = ( ( ( p ^ 2 ) - 1 ) / 2 )
              )
            )
          )
          /\
          A. a e. ( Base ` F )
            (
              a =/= ( 0g ` F )
              ->
              -.
              (
                a e. S
                <->
                ( ( 0g ` F ) ( -g ` F ) a ) e. S
              )
            )
        )
        ->
        (
          (
            #
            `
            (
              S
              i^i
              {
                x e. ( Base ` F ) |
                E. a e. S x = ( a ( +g ` F ) a )
              }
            )
          )
          mod
          2
        )
        =
        0
      )
  $.
$}
