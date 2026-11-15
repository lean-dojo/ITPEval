$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_b5: the nearest-integer-distance integral limit, assuming the
  Wallis product, is the natural logarithm of 4 divided by pi. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P83B5Dist(x) is the distance from a real x to the nearest integer. For a
  noninteger x, floor(x)+1 is its ceiling; for an integer x, the first branch
  is zero. Thus the conditional is exactly

    min(x - floor(x), ceiling(x) - x),

  and is equivalent to the absolute distance from x to a nearest integer in
  the Isabelle source.

  Both displayed maps are NN0-indexed real sequences. The finite product is
  over 1 through n, inclusively. The integral is set.mm's real Lebesgue
  integral over [1,n]. Its totalized value at n = 0 is irrelevant to the
  limit and the terms for every positive n are exactly the source interval
  integrals. The final declaration is one unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P83B5Dist $.

p83b5-distance-syntax $a class ( P83B5Dist x ) $.

p83b5-distance-definition $a |- (
  ( P83B5Dist x )
  =
  if (
    ( x - ( |_ ` x ) ) <_ ( ( ( |_ ` x ) + 1 ) - x ) ,
    ( x - ( |_ ` x ) ) ,
    ( ( ( |_ ` x ) + 1 ) - x )
  )
) $.

${
  $d i n x $.

  putnambench-putnam-1983-b5 $a |- (
    (
      n e. NN0 |->
        prod_ i e. ( 1 ... n )
          (
            (
              ( 2 x. i )
              /
              ( ( 2 x. i ) - 1 )
            )
            x.
            (
              ( 2 x. i )
              /
              ( ( 2 x. i ) + 1 )
            )
          )
    )
    ~~>
    ( _pi / 2 )
    ->
    (
      n e. NN0 |->
        (
          ( 1 / n )
          x.
          S. ( 1 [,] n )
            ( P83B5Dist ( n / x ) )
            _d x
        )
    )
    ~~>
    ( log ` ( 4 / _pi ) )
  ) $.
$}
