$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a1:
  among six distinct points in the real plane, the longest pairwise distance
  divided by the shortest pairwise distance is at least the square root of
  three. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P64A1R2 is the real coordinate plane and P64A1Dist is Euclidean distance.
  P64A1Dists forms the set of distances between distinct members of a point
  set. The real-order supremum and infimum are respectively the longest and
  shortest distances because a six-element point set has a nonempty finite
  distance set.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P64A1I P64A1R2 P64A1Dist P64A1Dists $.

p64a1-index-syntax $a class P64A1I $.
p64a1-plane-syntax $a class P64A1R2 $.
p64a1-distance-syntax $a class ( P64A1Dist A B ) $.
p64a1-distances-syntax $a class ( P64A1Dists S ) $.

p64a1-index-definition $a |- P64A1I = ( 1 ... 2 ) $.

p64a1-plane-definition $a |- P64A1R2 = ( RR ^m P64A1I ) $.

${
  $d A B j $.

  p64a1-distance-definition $a |- (
    P64A1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P64A1I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d S d p q $.

  p64a1-distances-definition $a |- (
    P64A1Dists S
  ) = {
    d e. RR |
    E. p e. S E. q e. S
      (
        p =/= q
        /\
        d = ( P64A1Dist p q )
      )
  } $.
$}

putnambench-putnam-1964-a1 $a |- A. S
  (
    (
      S C_ P64A1R2
      /\
      ( # ` S ) = 6
    )
    ->
    ( sqrt ` 3 ) <_
      (
        (
          sup ( ( P64A1Dists S ) , RR , < )
        )
        /
        (
          inf ( ( P64A1Dists S ) , RR , < )
        )
      )
  )
$.
