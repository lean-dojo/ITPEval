$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_b3: a sufficiently large set of two-by-two matrices whose
  entries are integral squares at most 200 contains two distinct commuting
  matrices. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The index set 0 ..^ 2 is the two-element carrier corresponding to Fin 2,
  and RR ^m ((0 ..^ 2) X. (0 ..^ 2)) is the set of real two-by-two
  matrices. Requiring every entry to equal m ^ 2 for some m in NN0 makes
  these matrices exactly the entrywise real images of the natural-valued
  matrices in the Lean and Isabelle sources and of the square-valued real
  matrices in the Rocq source. This entrywise embedding is injective and
  preserves matrix multiplication, so it also preserves distinctness and
  commutation.

  The entry restriction leaves only finitely many possible matrices, hence
  the extended SetMM cardinal # agrees with the finite cardinal notions in
  all three sources. RRfld maMul is SetMM's matrix multiplication. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A B S i j m $.

  putnambench-putnam-1990-b3 $a |- A. S
    (
      (
        (
          S C_
          (
            RR
            ^m
            ( ( 0 ..^ 2 ) X. ( 0 ..^ 2 ) )
          )
          /\
          A. A e. S
            A. i e. ( 0 ..^ 2 )
              A. j e. ( 0 ..^ 2 )
                E. m e. NN0
                  (
                    ( A ` <. i , j >. ) = ( m ^ 2 )
                    /\
                    ( A ` <. i , j >. ) <_ ; ; 2 0 0
                  )
        )
        /\
        ; ; ; ; 5 0 3 8 7 < ( # ` S )
      )
      ->
      E. A e. S E. B e. S
        (
          A =/= B
          /\
          (
            A
            (
              RRfld
              maMul
              <. ( 0 ..^ 2 ) , ( 0 ..^ 2 ) , ( 0 ..^ 2 ) >.
            )
            B
          )
          =
          (
            B
            (
              RRfld
              maMul
              <. ( 0 ..^ 2 ) , ( 0 ..^ 2 ) , ( 0 ..^ 2 ) >.
            )
            A
          )
        )
    )
  $.
$}
