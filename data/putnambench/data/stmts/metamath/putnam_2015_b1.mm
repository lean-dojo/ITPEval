$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b1: a twice continuously differentiable real function whose
  second derivative is differentiable and which has at least five distinct
  real zeros makes f + 6f' + 12f'' + 8f''' have at least two distinct real
  zeros. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of all total real-valued functions. Membership in
  ( ( C^n ` RR ) ` 2 ) expresses global continuous differentiability through
  order two, while requiring RR to be contained in the domain of the third
  entry of ( RR Dn F ) says that the second derivative is differentiable
  everywhere.

  SetMM's # function is the finite cardinality on finite sets and +oo on
  infinite sets. Thus the two cardinality inequalities say exactly that the
  corresponding zero sets have at least five and at least two distinct real
  elements, including when a zero set is infinite. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d F x $.

  putnambench-putnam-2015-b1 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          (
            F e. ( ( C^n ` RR ) ` 2 )
            /\
            RR C_ dom ( ( RR Dn F ) ` 3 )
          )
          /\
          5
          <_
          (
            #
            `
            {
              x e. RR |
                ( F ` x ) = 0
            }
          )
        )
        ->
        2
        <_
        (
          #
          `
          {
            x e. RR |
              (
                (
                  (
                    ( F ` x )
                    +
                    (
                      6
                      x.
                      ( ( ( RR Dn F ) ` 1 ) ` x )
                    )
                  )
                  +
                  (
                    ; ; 1 2
                    x.
                    ( ( ( RR Dn F ) ` 2 ) ` x )
                  )
                )
                +
                (
                  8
                  x.
                  ( ( ( RR Dn F ) ` 3 ) ` x )
                )
              )
              =
              0
          }
        )
      )
  $.
$}
