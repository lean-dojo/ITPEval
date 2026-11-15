$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_a2: no two distinct real square matrices of positive order
  satisfy A cubed equals B cubed, A squared times B equals B squared times
  A, and invertibility of the sum of their squares. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the carrier 0 ..^ n is the canonical n-element index set.
  Base ` ( ( 0 ..^ n ) Mat RRfld ) is the full set of real n-by-n matrices;
  simultaneous reindexing identifies it with either source's finite matrix
  type. The operations .r and +g are matrix multiplication and addition.

  Membership in Unit of this matrix ring means existence of a left and right
  multiplicative inverse, exactly the source condition
  Nonempty (Invertible (A ^ 2 + B ^ 2)). The annotated source solution is
  False, so its equivalence with the existential matrix condition is rendered
  as the negation below. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d A B n $.

  putnambench-putnam-1991-a2 $a |-
    A. n e. NN
      -.
      E. A e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
        E. B e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
          (
            A =/= B
            /\
            (
              (
                (
                  A
                  ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                  A
                )
                ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                A
              )
              =
              (
                (
                  B
                  ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                  B
                )
                ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                B
              )
              /\
              (
                (
                  (
                    A
                    ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                    A
                  )
                  ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                  B
                )
                =
                (
                  (
                    B
                    ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                    B
                  )
                  ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                  A
                )
                /\
                (
                  (
                    (
                      A
                      ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                      A
                    )
                    ( +g ` ( ( 0 ..^ n ) Mat RRfld ) )
                    (
                      B
                      ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                      B
                    )
                  )
                  e.
                  ( Unit ` ( ( 0 ..^ n ) Mat RRfld ) )
                )
              )
            )
          )
  $.
$}
