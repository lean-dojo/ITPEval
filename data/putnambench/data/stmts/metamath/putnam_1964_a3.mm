$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a3:
  an identity for the infinite sum of products of the two gaps created when
  successive distinct points form a dense sequence in the open unit interval.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  X, A, and B are real-valued sequences indexed by NN0. The first two
  hypotheses say that X is injective and has dense range in the open unit
  interval. For each n, A(n) and B(n) are the distances from X(n) to the
  supremum and infimum of the earlier points on its left and right, with zero
  and one included as endpoints. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A B X i n p $.

  putnambench-putnam-1964-a3 $a |- A. X e. ( RR ^m NN0 )
    A. A e. ( RR ^m NN0 )
      A. B e. ( RR ^m NN0 )
        (
          (
            (
              (
                (
                  ran X C_
                    { p e. RR | ( 0 < p /\ p < 1 ) }
                  /\
                  { p e. RR | ( 0 < p /\ p < 1 ) } C_
                    (
                      ( cls ` ( TopOpen ` RRfld ) )
                      `
                      ran X
                    )
                )
                /\
                X : NN0 -1-1-> RR
              )
              /\
              A =
                (
                  n e. NN0 |->
                    (
                      ( X ` n )
                      -
                      sup
                      (
                        (
                          { 0 }
                          u.
                          { p e. RR |
                            (
                              p < ( X ` n )
                              /\
                              E. i e. NN0
                                (
                                  i < n
                                  /\
                                  p = ( X ` i )
                                )
                            )
                          }
                        )
                        ,
                        RR
                        ,
                        <
                      )
                    )
                )
            )
            /\
            B =
              (
                n e. NN0 |->
                  (
                    inf
                    (
                      (
                        { 1 }
                        u.
                        { p e. RR |
                          (
                            ( X ` n ) < p
                            /\
                            E. i e. NN0
                              (
                                i < n
                                /\
                                p = ( X ` i )
                              )
                          )
                        }
                      )
                      ,
                      RR
                      ,
                      <
                    )
                    -
                    ( X ` n )
                  )
              )
          )
          ->
          sum_ n e. NN0
            (
              ( ( A ` n ) x. ( B ` n ) )
              x.
              ( ( A ` n ) + ( B ` n ) )
            )
            =
            ( 1 / 3 )
        )
$.
$}
