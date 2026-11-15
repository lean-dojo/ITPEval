$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b1: the maximum number of rational-coordinate points on a
  circle in the real plane whose center is not a rational point is two.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P08B1R2 is the real coordinate plane and P08B1Q2 is its subset of points
  with two rational coordinates. P08B1Dist is Euclidean distance.
  P08B1NCard implements the finite-cardinality convention of Lean's
  Set.ncard and Isabelle's card: it is zero for an infinite set.

  The first conjunct of the final assertion says that two rational points
  are attained by a circle with a nonrational center. The second conjunct
  gives the upper-bound clause for every natural cardinality attained by
  such a circle. Together they expand the source IsGreatest assertion with
  its annotated solution 2. Centers and radii retain their full real
  domains, including the source's unrestricted radius. Every declaration
  below is an unproved $a statement; this database contains no $p proof
  declaration.
$)

$c P08B1I P08B1R2 P08B1Q2 P08B1Dist P08B1NCard $.

p08b1-index-syntax $a class P08B1I $.
p08b1-plane-syntax $a class P08B1R2 $.
p08b1-rational-plane-syntax $a class P08B1Q2 $.
p08b1-distance-syntax $a class ( P08B1Dist A B ) $.
p08b1-ncard-syntax $a class P08B1NCard $.

p08b1-index-definition $a |- P08B1I = ( 1 ... 2 ) $.

p08b1-plane-definition $a |- P08B1R2 = ( RR ^m P08B1I ) $.

p08b1-rational-plane-definition $a |-
  P08B1Q2 = ( QQ ^m P08B1I ) $.

${
  $d A B k $.

  p08b1-distance-definition $a |- (
    P08B1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P08B1I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

p08b1-ncard-definition $a |- P08B1NCard =
  ( s e. _V |-> if ( s e. Fin , ( # ` s ) , 0 ) ) $.

${
  $d c n p r $.

  putnambench-putnam-2008-b1 $a |- (
    E. c e. P08B1R2
      E. r e. RR
        (
          c e/ P08B1Q2
          /\
          (
            P08B1NCard
            `
            {
              p e. P08B1Q2 |
              ( P08B1Dist p c ) = r
            }
          )
          =
          2
        )
    /\
    A. n e. NN0
      (
        E. c e. P08B1R2
          E. r e. RR
            (
              c e/ P08B1Q2
              /\
              (
                P08B1NCard
                `
                {
                  p e. P08B1Q2 |
                  ( P08B1Dist p c ) = r
                }
              )
              =
              n
            )
        ->
        n <_ 2
      )
  ) $.
$}
