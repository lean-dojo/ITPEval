$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_b6: a finite group of real square matrices with zero total
  trace has zero matrix sum. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The positive natural n has canonical index carrier 0 ..^ n, and G ranges
  over finite subsets of the full set of real-valued matrices on that
  carrier. RRfld maMul is SetMM's matrix multiplication. The group
  hypotheses state closure, membership of the actual identity matrix, and
  a right inverse in G for every member.

  Both trace and matrix addition are rendered by their finite coordinate
  sums. Thus the scalar hypothesis is the sum over G of the diagonal sums,
  while the conclusion says coordinatewise that the sum of all matrices in
  G is the zero matrix. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d G M g h i j n $.

  putnambench-putnam-1985-b6 $a |-
    A. n e. NN
      A. G e.
        ~P
        (
          RR
          ^m
          ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
        )
        (
          (
            G e. Fin
            /\
            (
              A. g e. G
                A. h e. G
                  (
                    g
                    (
                      RRfld
                      maMul
                      <.
                        ( 0 ..^ n ) ,
                        ( 0 ..^ n ) ,
                        ( 0 ..^ n )
                      >.
                    )
                    h
                  )
                  e. G
              /\
              (
                (
                  i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                    if ( i = j , 1 , 0 )
                )
                e. G
                /\
                A. g e. G
                  E. h e. G
                    (
                      g
                      (
                        RRfld
                        maMul
                        <.
                          ( 0 ..^ n ) ,
                          ( 0 ..^ n ) ,
                          ( 0 ..^ n )
                        >.
                      )
                      h
                    )
                    =
                    (
                      i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                        if ( i = j , 1 , 0 )
                    )
              )
            )
            /\
            (
              sum_ M e. G
                sum_ i e. ( 0 ..^ n )
                  ( M ` <. i , i >. )
            )
            =
            0
          )
          ->
          (
            i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
              sum_ M e. G
                ( M ` <. i , j >. )
          )
          =
          (
            i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
              0
          )
        )
  $.
$}
