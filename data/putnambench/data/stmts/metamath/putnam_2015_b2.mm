$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b2: the iterative process that removes the three smallest
  positive integers still present and their sum produces a sum ending in
  the decimal digits 2015. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  T is the natural-indexed sequence of remaining subsets of NN0, M assigns
  to every subset a triple indexed by 0 ..^ 3, and U is the sequence of
  sums. The cardinality hypothesis and the three attained-minimum
  characterizations are equivalent to the source's successive sInf/LEAST
  equations after deleting the previously selected entries.

  The recurrence removes the selected triple together with its sum. Since
  the residue 2015 is already four digits long, U(n) mod 10000 = 2015 is
  equivalent to the Lean least-significant-first digit prefix [5,1,0,2] and
  is exactly the Isabelle decimal-suffix condition. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

${
  $d M S T U n x $.

  putnambench-putnam-2015-b2 $a |-
    A. T e. ( ( ~P NN0 ) ^m NN0 )
      A. M e.
        (
          ( NN0 ^m ( 0 ..^ 3 ) )
          ^m
          ( ~P NN0 )
        )
        A. U e. ( NN0 ^m NN0 )
          (
            (
              (
                (
                  ( T ` 0 ) = NN
                  /\
                  A. S e. ( ~P NN0 )
                    (
                      3 <_ ( # ` S )
                      ->
                      (
                        (
                          (
                            ( ( M ` S ) ` 0 ) e. S
                            /\
                            A. x e. S
                              ( ( M ` S ) ` 0 ) <_ x
                          )
                          /\
                          (
                            ( ( M ` S ) ` 1 )
                            e.
                            ( S \ { ( ( M ` S ) ` 0 ) } )
                            /\
                            A. x e.
                              ( S \ { ( ( M ` S ) ` 0 ) } )
                              ( ( M ` S ) ` 1 ) <_ x
                          )
                        )
                        /\
                        (
                          ( ( M ` S ) ` 2 )
                          e.
                          (
                            S
                            \
                            {
                              ( ( M ` S ) ` 0 ) ,
                              ( ( M ` S ) ` 1 )
                            }
                          )
                          /\
                          A. x e.
                            (
                              S
                              \
                              {
                                ( ( M ` S ) ` 0 ) ,
                                ( ( M ` S ) ` 1 )
                              }
                            )
                            ( ( M ` S ) ` 2 ) <_ x
                        )
                      )
                    )
                )
                /\
                A. n e. NN0
                  ( U ` n )
                  =
                  (
                    (
                      ( ( M ` ( T ` n ) ) ` 0 )
                      +
                      ( ( M ` ( T ` n ) ) ` 1 )
                    )
                    +
                    ( ( M ` ( T ` n ) ) ` 2 )
                  )
              )
              /\
              A. n e. NN0
                ( T ` ( n + 1 ) )
                =
                (
                  ( T ` n )
                  \
                  (
                    {
                      ( ( M ` ( T ` n ) ) ` 0 ) ,
                      ( ( M ` ( T ` n ) ) ` 1 ) ,
                      ( ( M ` ( T ` n ) ) ` 2 )
                    }
                    u.
                    { ( U ` n ) }
                  )
                )
            )
            ->
            E. n e. NN0
              (
                ( U ` n )
                mod
                ( ; ; ; ; 1 0 0 0 0 )
              )
              =
              ( ; ; ; 2 0 1 5 )
          )
  $.
$}
