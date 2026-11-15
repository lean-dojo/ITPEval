$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b6: four square matrices over an arbitrary field satisfying
  two symmetry conditions and a block inverse identity satisfy the
  corresponding transposed identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The positive natural n has index carrier 0 ..^ n. For every SetMM field
  structure F, Base ` ( ( 0 ..^ n ) Mat F ) is exactly the set of square
  matrices on that carrier with entries in Base ` F. The operation .r of
  this matrix ring is matrix multiplication, tpos is matrix transpose, -g
  is matrix subtraction, and 1r is the identity matrix.

  Thus the two first conjuncts state that A times transpose B and C times
  transpose D are symmetric. The third conjunct and the conclusion are the
  source matrix identities. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A B C D F n $.

  putnambench-putnam-1986-b6 $a |-
    A. n e. NN
      A. F
        A. A e. ( Base ` ( ( 0 ..^ n ) Mat F ) )
          A. B e. ( Base ` ( ( 0 ..^ n ) Mat F ) )
            A. C e. ( Base ` ( ( 0 ..^ n ) Mat F ) )
              A. D e. ( Base ` ( ( 0 ..^ n ) Mat F ) )
                (
                  F e. Field
                  ->
                  (
                    (
                      (
                        (
                          A
                          ( .r ` ( ( 0 ..^ n ) Mat F ) )
                          tpos B
                        )
                        =
                        tpos
                        (
                          A
                          ( .r ` ( ( 0 ..^ n ) Mat F ) )
                          tpos B
                        )
                      )
                      /\
                      (
                        (
                          C
                          ( .r ` ( ( 0 ..^ n ) Mat F ) )
                          tpos D
                        )
                        =
                        tpos
                        (
                          C
                          ( .r ` ( ( 0 ..^ n ) Mat F ) )
                          tpos D
                        )
                      )
                    )
                    /\
                    (
                      (
                        A
                        ( .r ` ( ( 0 ..^ n ) Mat F ) )
                        tpos D
                      )
                      ( -g ` ( ( 0 ..^ n ) Mat F ) )
                      (
                        B
                        ( .r ` ( ( 0 ..^ n ) Mat F ) )
                        tpos C
                      )
                    )
                    =
                    ( 1r ` ( ( 0 ..^ n ) Mat F ) )
                  )
                  ->
                  (
                    (
                      tpos A
                      ( .r ` ( ( 0 ..^ n ) Mat F ) )
                      D
                    )
                    ( -g ` ( ( 0 ..^ n ) Mat F ) )
                    (
                      tpos C
                      ( .r ` ( ( 0 ..^ n ) Mat F ) )
                      B
                    )
                  )
                  =
                  ( 1r ` ( ( 0 ..^ n ) Mat F ) )
                )
  $.
$}
