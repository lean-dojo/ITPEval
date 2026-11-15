$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a3: existence of two cells in a three-by-2024 standard
  tableau whose relative order has probability between one third and two
  thirds, inclusive. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P24A3Rows, P24A3Cols, P24A3Cells, and P24A3Values are respectively
  1 ... 3, 1 ... 2024, their Cartesian product, and 1 ... 6072.
  P24A3Tableaux is the finite set of bijections from the cells to the
  values that are strictly increasing in each row and each column.

  The Lean source instead uses total maps on NN0 X. NN0 that vanish outside
  P24A3Cells. Restriction to P24A3Cells and extension by zero are inverse
  bijections between that set and P24A3Tableaux, and they preserve every
  displayed cell comparison. Thus the two finite cardinalities and their
  quotient are unchanged.

  Pairwise strict increase is exactly StrictMonoOn on each finite interval.
  The four cell coordinates remain internally existentially quantified, and
  the closed interval retains both source probability bounds. The annotated
  solution is True, so the source biconditional is equivalent to the final
  existence assertion. Every declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

$c P24A3Rows P24A3Cols P24A3Cells P24A3Values P24A3Tableaux $.

p24a3-rows-syntax $a class P24A3Rows $.
p24a3-cols-syntax $a class P24A3Cols $.
p24a3-cells-syntax $a class P24A3Cells $.
p24a3-values-syntax $a class P24A3Values $.
p24a3-tableaux-syntax $a class P24A3Tableaux $.

p24a3-rows-definition $a |- P24A3Rows = ( 1 ... 3 ) $.

p24a3-cols-definition $a |-
  P24A3Cols = ( 1 ... ( ; ; ; 2 0 2 4 ) ) $.

p24a3-cells-definition $a |-
  P24A3Cells = ( P24A3Rows X. P24A3Cols ) $.

p24a3-values-definition $a |-
  P24A3Values = ( 1 ... ( ; ; ; 6 0 7 2 ) ) $.

${
  $d T i j k l $.

  p24a3-tableaux-definition $a |- P24A3Tableaux =
    {
      T e. ( P24A3Values ^m P24A3Cells ) |
      (
        T : P24A3Cells -1-1-onto-> P24A3Values
        /\
        (
          A. j e. P24A3Cols
            A. i e. P24A3Rows
              A. k e. P24A3Rows
                (
                  i < k
                  ->
                  ( T ` <. i , j >. ) < ( T ` <. k , j >. )
                )
          /\
          A. i e. P24A3Rows
            A. j e. P24A3Cols
              A. l e. P24A3Cols
                (
                  j < l
                  ->
                  ( T ` <. i , j >. ) < ( T ` <. i , l >. )
                )
        )
      )
    } $.
$}

${
  $d T a b c d $.

  putnambench-putnam-2024-a3 $a |-
    E. a e. P24A3Rows
      E. b e. P24A3Cols
        E. c e. P24A3Rows
          E. d e. P24A3Cols
            (
              (
                (
                  #
                  `
                  {
                    T e. P24A3Tableaux |
                    ( T ` <. a , b >. ) < ( T ` <. c , d >. )
                  }
                )
                /
                ( # ` P24A3Tableaux )
              )
              e.
              ( ( 1 / 3 ) [,] ( 2 / 3 ) )
            )
  $.
$}
