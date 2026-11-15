$(
  Statement-only formalization of Thousand Theorems corpus artifact Q220680
  (thousand-theorems__metamath__Q220680), "Banach fixed-point theorem": a
  contraction on a complete extended metric space has a fixed point approached
  by the iterates from any starting point at finite distance from its image,
  with the explicit geometric extended-distance bound. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  D e. ( *Met ` X ) is SetMM's native extended metric on the arbitrary
  carrier X, so distances take values in the extended reals and may equal
  +oo. The complete-space hypothesis uses the complete uniform space induced
  by D; its topology is the extended-metric topology.

  K ranges over all finite nonnegative reals, and K < 1 together with the
  displayed Lipschitz inequality is exactly ContractingWith K f. IterComp is
  SetMM's native finite-iteration operator, including the identity iterate at
  n = 0. The relation ~~>t expresses convergence of that iterate sequence in
  the topology induced by D. Extended-real multiplication *e and division /e
  render the source error estimate; 1 - K is positive and finite.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  $d D K X f n u v x y $.

  thousand-theorems-q220680-banach-fixed-point $a |-
    A. X A. D A. K e. ( 0 [,) +oo ) A. f A. x
      (
        (
          D e. ( *Met ` X )
          /\
          (
            ( toUnifSp ` ( metUnif ` D ) ) e. CUnifSp
            /\
            (
              f : X --> X
              /\
              x e. X
            )
          )
        )
        ->
        (
          (
            K < 1
            /\
            (
              A. u e. X A. v e. X
                (
                  ( ( f ` u ) D ( f ` v ) )
                  <_
                  ( K *e ( u D v ) )
                )
              /\
              ( x D ( f ` x ) ) =/= +oo
            )
          )
          ->
          E. y e. X
            (
              ( f ` y ) = y
              /\
              (
                ( n e. NN0 |->
                    (
                      ( ( IterComp ` f ) ` n )
                      `
                      x
                    )
                )
                (
                  ~~>t
                  `
                  ( unifTop ` ( metUnif ` D ) )
                )
                y
                /\
                A. n e. NN0
                  (
                    (
                      (
                        ( ( IterComp ` f ) ` n )
                        `
                        x
                      )
                      D
                      y
                    )
                    <_
                    (
                      (
                        ( x D ( f ` x ) )
                        *e
                        ( K ^ n )
                      )
                      /e
                      ( 1 - K )
                    )
                  )
              )
            )
        )
      )
  $.
$}
