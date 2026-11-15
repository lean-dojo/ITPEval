$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a2: determinant of a real matrix with constant strict upper
  and lower triangles and prescribed diagonal entries. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The positive natural n has canonical index carrier 0 ..^ n. The diagonal
  data c, matrix q, and polynomial function p range over their full real
  function spaces. The displayed hypotheses define q entrywise and define
  p(x) as the product of c(i)-x over every index.

  The arbitrary n-element carrier and rank bijection in the Isabelle source
  transport to 0 ..^ n by simultaneous reindexing of rows and columns. This
  preserves both the determinant and the indexed product, yielding exactly
  the Fin n presentation in the Lean source.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c i j n p q x $.

  putnambench-putnam-1978-a2 $a |-
    A. n e. NN
    A. a e. RR
    A. b e. RR
    A. c e. ( RR ^m ( 0 ..^ n ) )
    A. q e.
      (
        RR
        ^m
        ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
      )
    A. p e. ( RR ^m RR )
      (
        (
          a =/= b
          /\
          (
            q
            =
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                if
                (
                  i < j ,
                  a ,
                  if ( j < i , b , ( c ` i ) )
                )
            )
          )
          /\
          p
          =
          (
            x e. RR |->
              prod_ i e. ( 0 ..^ n )
                ( ( c ` i ) - x )
          )
        )
        ->
        (
          (
            ( ( 0 ..^ n ) maDet RRfld )
            `
            q
          )
          =
          (
            (
              ( b x. ( p ` a ) )
              -
              ( a x. ( p ` b ) )
            )
            /
            ( b - a )
          )
        )
      )
  $.
$}
