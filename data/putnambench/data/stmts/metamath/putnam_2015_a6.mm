$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a6: for positive dimension, intertwined real square matrices
  with the same characteristic polynomial satisfy the stated determinant
  identity for every real square matrix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, 0 ..^ n is the canonical n-element index set, and
  Base ` ((0 ..^ n) Mat RRfld) is the full set of real n-by-n matrices.
  The ring operations .r and -g are ordinary matrix multiplication and
  subtraction. The function (0 ..^ n) CharPlyMat RRfld is SetMM's
  characteristic polynomial det(tI-A), and (0 ..^ n) maDet RRfld is the
  determinant.

  Thus the antecedent is exactly AM = MB together with equality of the
  characteristic polynomials of A and B, and the conclusion retains the
  universal quantifier over every real n-by-n matrix X. The final declaration
  is the single unproved $a corpus statement.
$)

${
  $d A B M X n $.

  putnambench-putnam-2015-a6 $a |- A. n e. NN
    A. A e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
      A. B e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
        A. M e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
          (
            (
              (
                A
                ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                M
              )
              =
              (
                M
                ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                B
              )
              /\
              (
                ( ( ( 0 ..^ n ) CharPlyMat RRfld ) ` A )
                =
                ( ( ( 0 ..^ n ) CharPlyMat RRfld ) ` B )
              )
            )
            ->
            A. X e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
              (
                (
                  ( ( 0 ..^ n ) maDet RRfld )
                  `
                  (
                    A
                    ( -g ` ( ( 0 ..^ n ) Mat RRfld ) )
                    (
                      M
                      ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                      X
                    )
                  )
                )
                =
                (
                  ( ( 0 ..^ n ) maDet RRfld )
                  `
                  (
                    B
                    ( -g ` ( ( 0 ..^ n ) Mat RRfld ) )
                    (
                      X
                      ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                      M
                    )
                  )
                )
              )
          )
  $.
$}
