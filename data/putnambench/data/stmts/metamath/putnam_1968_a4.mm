$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_a4: the sum of squared pairwise distances among n points on
  the unit sphere in real three-space is at most n squared. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P68A4R3 is real coordinate three-space. P68A4NormSq is the squared
  Euclidean norm, and P68A4DistSq is squared Euclidean distance. Thus the
  unit-sphere equation P68A4NormSq A = 1 is equivalent to dist 0 A = 1,
  while P68A4DistSq A B is exactly (dist A B)^2.

  The ordinal n is the n-element carrier Fin n, and S is an arbitrary
  n-indexed family, so repeated points remain allowed. The displayed sum
  takes each unordered pair once. The Rocq source instead takes both ordered
  orientations and has bound 2 * n^2; symmetry of squared distance makes
  that formulation exactly twice this one.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P68A4R3 P68A4NormSq P68A4DistSq $.

p68a4-space-syntax $a class P68A4R3 $.
p68a4-norm-square-syntax $a class ( P68A4NormSq A ) $.
p68a4-distance-square-syntax $a class ( P68A4DistSq A B ) $.

p68a4-space-definition $a |- P68A4R3 = ( RR ^m 3 ) $.

${
  $d A k $.

  p68a4-norm-square-definition $a |- (
    P68A4NormSq A
  ) = (
    sum_ k e. 3
      ( ( A ` k ) ^ 2 )
  ) $.
$}

${
  $d A B k $.

  p68a4-distance-square-definition $a |- (
    P68A4DistSq A B
  ) = (
    sum_ k e. 3
      ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
  ) $.
$}

${
  $d S i j n $.

  putnambench-putnam-1968-a4 $a |- A. n e. NN0
    A. S e. ( P68A4R3 ^m n )
      (
        A. i e. n
          ( P68A4NormSq ( S ` i ) ) = 1
        ->
        (
          sum_ i e. n
            sum_ j e. n
              if (
                i < j ,
                ( P68A4DistSq ( S ` i ) ( S ` j ) ) ,
                0
              )
        )
        <_
        ( n ^ 2 )
      )
  $.
$}
