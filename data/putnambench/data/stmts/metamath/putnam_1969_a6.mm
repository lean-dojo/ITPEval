$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_a6: convergence of a real sequence from convergence of the
  sequence formed by adding its preceding term to twice its current term.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  X and Y range over all real-valued sequences indexed by the nonnegative
  integers. The recurrence is imposed exactly at every natural index n at
  least two. Each use of set.mm's real-sequence convergence relation keeps
  the corresponding real limit existentially quantified, as in all three
  ground-truth formalizations.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d C X Y c n $.

  putnambench-putnam-1969-a6 $a |-
    A. X e. ( RR ^m NN0 )
    A. Y e. ( RR ^m NN0 )
      (
        (
          A. n e. NN0
            (
              2 <_ n
              ->
              ( Y ` n )
              =
              (
                ( X ` ( n - 1 ) )
                +
                ( 2 x. ( X ` n ) )
              )
            )
          /\
          E. c e. RR
            (
              n e. NN0 |->
                ( Y ` n )
            )
            ~~>
            c
        )
        ->
        E. C e. RR
          (
            n e. NN0 |->
              ( X ` n )
          )
          ~~>
          C
      )
  $.
$}
