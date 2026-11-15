$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_b3: a lower bound for the probability of the intersection
  of events with only nearest-neighbor dependence. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P is a set.mm probability measure and E is an n-event family indexed by
  0 ..^ n. Pairwise independence for non-neighboring events is expressed
  by its defining equation

      P(E_i intersection E_j) = P(E_i) * P(E_j).

  The recurrence is indexed from u_0 and u_1, matching the published
  problem. The final declaration is the single unproved $a corpus
  statement; there is no $p proof declaration in this file.
$)

${
  $d P E u n a i j k $.

  putnambench-putnam-1976-b3 $a |-
    A. P e. Prob
    A. n e. NN
    A. a e. RR
    A. u e. ( RR ^m NN0 )
    A. E e. ( ( dom P ) ^m ( 0 ..^ n ) )
      (
        (
          (
            ( 0 <_ a /\ a < ( 1 / 4 ) )
            /\
            ( ( u ` 0 ) = 1 /\ ( u ` 1 ) = ( 1 - a ) )
          )
          /\
          (
            (
              A. k e. NN
                ( u ` ( k + 1 ) )
                =
                ( ( u ` k ) - ( a x. ( u ` ( k - 1 ) ) ) )
            )
            /\
            A. k e. NN0 0 < ( u ` k )
          )
        )
        /\
        (
          (
            A. i e. ( 0 ..^ n )
              ( 1 - a ) <_ ( P ` ( E ` i ) )
          )
          /\
          A. i e. ( 0 ..^ n )
            A. j e. ( 0 ..^ n )
              (
                (
                  ( ( i + 1 ) < j \/ ( j + 1 ) < i )
                  ->
                  ( P ` ( ( E ` i ) i^i ( E ` j ) ) )
                  =
                  ( ( P ` ( E ` i ) ) x. ( P ` ( E ` j ) ) )
                )
              )
        )
        ->
        ( u ` n )
        <_
        (
          P `
          |^|_ i e. ( 0 ..^ n ) ( E ` i )
        )
      )
  $.
$}
