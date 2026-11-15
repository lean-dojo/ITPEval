$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_a5: the proposed implication from ABAB being the zero real
  square matrix to BABA being the zero matrix is false. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ n is the n-element carrier corresponding to Fin n,
  and RR ^m ((0 ..^ n) X. (0 ..^ n)) is the full set of real n-by-n
  matrices. RRfld maMul is SetMM's matrix multiplication on that carrier.
  The constant maps in the two equalities are the zero matrix.

  Negating the universally quantified implication is exactly its
  equivalence with the source's specified solution False. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d A B i j n $.

  putnambench-putnam-1990-a5 $a |- -.
    A. n e. NN
      A. A e.
        (
          RR
          ^m
          ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
        )
        A. B e.
          (
            RR
            ^m
            ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
          )
          (
            (
              (
                (
                  A
                  (
                    RRfld
                    maMul
                    <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
                  )
                  B
                )
                (
                  RRfld
                  maMul
                  <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
                )
                A
              )
              (
                RRfld
                maMul
                <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
              )
              B
            )
            =
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                0
            )
            ->
            (
              (
                (
                  B
                  (
                    RRfld
                    maMul
                    <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
                  )
                  A
                )
                (
                  RRfld
                  maMul
                  <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
                )
                B
              )
              (
                RRfld
                maMul
                <. ( 0 ..^ n ) , ( 0 ..^ n ) , ( 0 ..^ n ) >.
              )
              A
            )
            =
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                0
            )
          )
  $.
$}
