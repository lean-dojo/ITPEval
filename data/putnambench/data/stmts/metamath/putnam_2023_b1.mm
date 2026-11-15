$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b1: the number of coin configurations reachable by diagonal
  legal moves on an m-by-n grid is the binomial coefficient
  (m+n-2 choose m-1). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P23B1States is the full function space from NN0 X. NN0 to {0,1}.
  Replacing a curried Bool-valued function by its uncurried {0,1}-valued
  function is a bijective relabeling and preserves the source's infinite
  ambient domain. P23B1Init m n is 1 exactly on the initial rectangle
  i < m-1 and j < n-1.

  P23B1Move m n C D expands one legal move: a 1 at (i,j), with the other
  three cells of its southeast unit square equal to 0, is moved to
  (i+1,j+1), and every other value is unchanged. P23B1Game m n G is a
  nonempty finite word of states beginning at P23B1Init m n and related
  by P23B1Move at every consecutive pair. A one-state word represents the
  possibly empty move sequence.

  The restricted class in the final assertion is therefore exactly the
  set of reachable configurations. Set.mm's # is finite cardinality here,
  and _C is the binomial-coefficient operation. The final declaration
  inlines the solution annotation from the Lean and Isabelle sources.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P23B1States P23B1Init P23B1Move P23B1Game $.

p23b1-states-syntax $a class P23B1States $.
p23b1-init-syntax $a class ( P23B1Init m n ) $.
p23b1-move-syntax $a wff ( P23B1Move m n C D ) $.
p23b1-game-syntax $a wff ( P23B1Game m n G ) $.

p23b1-states-definition $a |-
  P23B1States = ( { 0 , 1 } ^m ( NN0 X. NN0 ) )
$.

${
  $d m n x $.

  p23b1-init-definition $a |- ( P23B1Init m n ) =
    ( x e. ( NN0 X. NN0 ) |->
      if
      (
        (
          ( 1st ` x ) < ( m - 1 )
          /\
          ( 2nd ` x ) < ( n - 1 )
        ) ,
        1 ,
        0
      )
    )
  $.
$}

${
  $d C D i j m n x $.

  p23b1-move-definition $a |- (
    ( P23B1Move m n C D )
    <->
    E. i e. NN0 E. j e. NN0
      (
        i < ( m - 1 )
        /\
        (
          j < ( n - 1 )
          /\
          (
            ( C ` <. i , j >. ) = 1
            /\
            (
              ( C ` <. ( i + 1 ) , j >. ) = 0
              /\
              (
                ( C ` <. i , ( j + 1 ) >. ) = 0
                /\
                (
                  ( C ` <. ( i + 1 ) , ( j + 1 ) >. ) = 0
                  /\
                  (
                    ( D ` <. i , j >. ) = 0
                    /\
                    (
                      ( D ` <. ( i + 1 ) , j >. ) = 0
                      /\
                      (
                        ( D ` <. i , ( j + 1 ) >. ) = 0
                        /\
                        (
                          ( D ` <. ( i + 1 ) , ( j + 1 ) >. ) = 1
                          /\
                          A. x e. ( NN0 X. NN0 )
                            (
                              (
                                x =/= <. i , j >.
                                /\
                                (
                                  x =/= <. ( i + 1 ) , j >.
                                  /\
                                  (
                                    x =/= <. i , ( j + 1 ) >.
                                    /\
                                    x =/= <. ( i + 1 ) , ( j + 1 ) >.
                                  )
                                )
                              )
                              ->
                              ( C ` x ) = ( D ` x )
                            )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d G i m n $.

  p23b1-game-definition $a |- (
    ( P23B1Game m n G )
    <->
    (
      G e. ( Word P23B1States \ { (/) } )
      /\
      (
        ( G ` 0 ) = ( P23B1Init m n )
        /\
        A. i e. ( 0 ..^ ( ( # ` G ) - 1 ) )
          (
            P23B1Move
              m
              n
              ( G ` i )
              ( G ` ( i + 1 ) )
          )
      )
    )
  ) $.
$}

${
  $d C G m n $.

  putnambench-putnam-2023-b1 $a |-
    A. m e. NN0 A. n e. NN0
      (
        (
          1 < m
          /\
          1 < n
        )
        ->
        (
          #
          `
          {
            C e. P23B1States |
            E. G e. ( Word P23B1States \ { (/) } )
              (
                ( P23B1Game m n G )
                /\
                C = ( G ` ( ( # ` G ) - 1 ) )
              )
          }
        )
        =
        ( ( m + n - 2 ) _C ( m - 1 ) )
      )
  $.
$}
