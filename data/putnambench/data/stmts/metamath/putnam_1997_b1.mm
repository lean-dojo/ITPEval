$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_b1: for every positive integer n, the stated finite sum of
  minima of distances to the nearest integer equals n. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  P97B1Dist(x) is the distance from a real x to the nearest integer. For a
  noninteger x, floor(x)+1 is its ceiling; for an integer x, the first branch
  is zero. Thus the conditional is exactly

    min(x - floor(x), ceiling(x) - x).

  The outer conditional is min(P97B1Dist(m/(6n)), P97B1Dist(m/(3n))).
  The interval 1 ... 6n-1 is inclusive, so the sum and the positive-integer
  quantifier are exactly those in the sources. Inlining F is definitionally
  equivalent to the Lean and Isabelle defining equations, while the Rocq
  source identifies the solution value as n. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

$c P97B1Dist $.

p97b1-distance-syntax $a class ( P97B1Dist A ) $.

p97b1-distance-definition $a |- (
  ( P97B1Dist A )
  =
  if (
    ( A - ( |_ ` A ) ) <_ ( ( ( |_ ` A ) + 1 ) - A ) ,
    ( A - ( |_ ` A ) ) ,
    ( ( ( |_ ` A ) + 1 ) - A )
  )
) $.

${
  $d m n $.

  putnambench-putnam-1997-b1 $a |- A. n e. NN
    (
      sum_ m e. ( 1 ... ( ( 6 x. n ) - 1 ) )
        if (
          ( P97B1Dist ( m / ( 6 x. n ) ) )
            <_
          ( P97B1Dist ( m / ( 3 x. n ) ) ) ,
          ( P97B1Dist ( m / ( 6 x. n ) ) ) ,
          ( P97B1Dist ( m / ( 3 x. n ) ) )
        )
    )
    =
    n
  $.
$}
