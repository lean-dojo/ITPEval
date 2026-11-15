$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_b6: impossibility of expressing the positive natural numbers
  as the union of three pairwise disjoint floor-sequence sets with positive
  real parameters. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P95B6S is the set-valued map sending a real a to the natural numbers x
  for which x = floor(n*a) for some positive integer n. The codomain
  restriction NN0 preserves the source set's full natural-number domain,
  including a possible value zero. SetMM's |_ operation is real floor.

  The final assertion quantifies the three parameters internally over RR,
  retains their strict positivity, states all three pairwise-disjointness
  conditions as empty intersections, and identifies their union with NN,
  SetMM's class of positive integers. The declaration is an unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

$c P95B6S $.

p95b6-set-syntax $a class P95B6S $.

${
  $d a n x $.

  p95b6-set-definition $a |- P95B6S =
    (
      a e. RR |->
        {
          x e. NN0 |
          E. n e. NN
            x = ( |_ ` ( n x. a ) )
        }
    )
  $.
$}

${
  $d a b c $.

  putnambench-putnam-1995-b6 $a |-
    -.
    E. a e. RR E. b e. RR E. c e. RR
      (
        (
          ( 0 < a /\ 0 < b )
          /\
          0 < c
        )
        /\
        (
          (
            (
              ( ( P95B6S ` a ) i^i ( P95B6S ` b ) )
              =
              (/)
            )
            /\
            (
              ( ( P95B6S ` b ) i^i ( P95B6S ` c ) )
              =
              (/)
            )
          )
          /\
          (
            (
              ( ( P95B6S ` a ) i^i ( P95B6S ` c ) )
              =
              (/)
            )
            /\
            NN
            =
            (
              ( ( P95B6S ` a ) u. ( P95B6S ` b ) )
              u.
              ( P95B6S ` c )
            )
          )
        )
      )
  $.
$}
