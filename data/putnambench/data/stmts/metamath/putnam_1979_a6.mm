$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a6: a reciprocal-distance sum bound for finitely many real
  points in the unit interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the class RR ^m ( 1 ... n ) contains every n-term real
  family. It is equivalent to the source functions restricted to their used
  indices; the bijection j |-> j + 1 carries Lean's indices 0 through n - 1
  to Isabelle's indices 1 through n and changes 2j + 1 into 2i - 1.

  The existentially quantified x remains in the unit interval, is distinct
  from every family value, and satisfies the same finite reciprocal-distance
  bound. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d i n p x $.

  putnambench-putnam-1979-a6 $a |- A. n e. NN0
    A. p e. ( RR ^m ( 1 ... n ) )
      (
        A. i e. ( 1 ... n )
          (
            0 <_ ( p ` i )
            /\
            ( p ` i ) <_ 1
          )
        ->
        E. x e. RR
          (
            (
              0 <_ x
              /\
              x <_ 1
            )
            /\
            (
              (
                A. i e. ( 1 ... n ) x =/= ( p ` i )
              )
              /\
              (
                sum_ i e. ( 1 ... n )
                  (
                    1
                    /
                    ( abs ` ( x - ( p ` i ) ) )
                  )
              )
              <_
              (
                ( 8 x. n )
                x.
                (
                  sum_ i e. ( 1 ... n )
                    (
                      1
                      /
                      ( ( 2 x. i ) - 1 )
                    )
                )
              )
            )
          )
      )
  $.
$}
