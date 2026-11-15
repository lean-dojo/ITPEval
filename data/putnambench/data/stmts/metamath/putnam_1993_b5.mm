$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_b5: there do not exist four points in the real Euclidean
  plane whose six pairwise distances are all odd integers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P93B5I is the two-coordinate index set, P93B5R2 is the full real
  coordinate plane, and P93B5Dist is ordinary Euclidean distance. The
  ordinal 4 is the four-element carrier corresponding to Fin 4, and Odd
  is set.mm's class of odd integers.

  The final declaration negates the internally existential four-point
  configuration. It retains universal quantification over every distinct
  pair of indices and an internal odd-integer witness for each distance.
  Every declaration below is an unproved $a statement, not a proof.
$)

$c P93B5I P93B5R2 P93B5Dist $.

p93b5-index-syntax $a class P93B5I $.
p93b5-plane-syntax $a class P93B5R2 $.
p93b5-distance-syntax $a class ( P93B5Dist A B ) $.

p93b5-index-definition $a |- P93B5I = ( 1 ... 2 ) $.

p93b5-plane-definition $a |- P93B5R2 = ( RR ^m P93B5I ) $.

${
  $d A B k $.

  p93b5-distance-definition $a |- (
    P93B5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P93B5I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d i j n p $.

  putnambench-putnam-1993-b5 $a |- -.
    E. p e. ( P93B5R2 ^m 4 )
      A. i e. 4 A. j e. 4
        (
          i =/= j
          ->
          E. n e. Odd
            ( P93B5Dist ( p ` i ) ( p ` j ) ) = n
        )
  $.
$}
