$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a6: a finite-dimensional linear endomorphism with n+1
  eigenvectors such that every n of them are linearly independent is a
  scalar multiple of the identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V ranges over SetMM vector-space structures whose scalar structure is a
  field, Base ` V is the vector carrier, and dim ` V is its dimension.
  A belongs to the SetMM class of linear endomorphisms V LMHom V. The set E
  consists of n+1 nonzero eigenvectors, with the eigenvalue witness remaining
  internally existential.

  The source condition on every injective Fin n-indexed selection is written
  in the equivalent form that every n-element subset S of E belongs to
  LIndS ` V. The conclusion is the pointwise form of equality between A and
  a scalar multiple of the identity. The source solution proposition is
  annotated as True, so its biconditional reduces to the assertion below.
  The n = 0 case is vacuous because a zero-dimensional vector space has no
  nonzero eigenvector, matching the positive-dimension Isabelle formulation.
  The final declaration is a single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d A E S V c n x $.

  putnambench-putnam-1988-a6 $a |-
    A. V A. n e. NN0 A. A e. ( V LMHom V ) A. E
      (
        (
          (
            V e. LVec
            /\
            ( Scalar ` V ) e. Field
          )
          /\
          (
            ( dim ` V ) = n
            /\
            (
              E
              C_
              {
                x e. ( ( Base ` V ) \ { ( 0g ` V ) } ) |
                E. c e. ( Base ` ( Scalar ` V ) )
                  ( A ` x ) = ( c ( .s ` V ) x )
              }
              /\
              (
                ( # ` E ) = ( n + 1 )
                /\
                A. S
                  (
                    (
                      S C_ E
                      /\
                      ( # ` S ) = n
                    )
                    ->
                    S e. ( LIndS ` V )
                  )
              )
            )
          )
        )
        ->
        E. c e. ( Base ` ( Scalar ` V ) )
          A. x e. ( Base ` V )
            ( A ` x ) = ( c ( .s ` V ) x )
      )
  $.
$}
