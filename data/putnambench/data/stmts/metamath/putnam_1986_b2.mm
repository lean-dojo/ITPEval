$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b2: the ordered complex difference triples arising from the
  simultaneous polynomial equations are exactly four explicit triples.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM represents an ordered triple as <. a , b , c >., definitionally the
  nested pair <. <. a , b >. , c >. The left side of the biconditional lists
  exactly the four solution triples formalized in the Rocq source and
  annotated in the Lean and Isabelle sources. The right side retains the
  internally existential complex numbers x, y, and z and both simultaneous
  equations from every ground-truth statement.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d t x y z $.

  putnambench-putnam-1986-b2 $a |- A. t e. ( ( CC X. CC ) X. CC )
    (
      (
        t = <. 0 , 0 , 0 >.
        \/
        (
          t = <. 0 , ( -u 1 ) , 1 >.
          \/
          (
            t = <. 1 , 0 , ( -u 1 ) >.
            \/
            t = <. ( -u 1 ) , 1 , 0 >.
          )
        )
      )
      <->
      E. x e. CC E. y e. CC E. z e. CC
        (
          t = <. ( x - y ) , ( y - z ) , ( z - x ) >.
          /\
          (
            (
              ( x x. ( x - 1 ) )
              +
              ( ( 2 x. y ) x. z )
            )
            =
            (
              ( y x. ( y - 1 ) )
              +
              ( ( 2 x. z ) x. x )
            )
            /\
            (
              ( y x. ( y - 1 ) )
              +
              ( ( 2 x. z ) x. x )
            )
            =
            (
              ( z x. ( z - 1 ) )
              +
              ( ( 2 x. x ) x. y )
            )
          )
        )
    )
  $.
$}
