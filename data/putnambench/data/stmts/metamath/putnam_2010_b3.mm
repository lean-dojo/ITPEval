$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b3: characterization of the positive integers for which every
  distribution of 2010n balls among 2010 labeled boxes can be equalized by
  the prescribed exact-size transfers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P2010B3I is the 2010-element ordinal 0 ..^ 2010, representing Fin 2010.
  A distribution is an NN0-valued function on this carrier. A trajectory is
  an NN0-indexed family of distributions. P2010B3Trans P T says that at each
  time t < T, one chooses distinct indices i and j, removes exactly i+1 balls
  from box i, adds them to box j, and leaves every other box unchanged.

  The corpus assertion quantifies over every initial distribution with total
  2010n, keeps the trajectory and terminal time existential, and requires the
  terminal distribution to be constantly n. The right side gives the intended
  solution set {n in NN | 1005 <= n}. The auxiliary $a declarations are
  syntax and faithful definitions; the final $a is the single unproved corpus
  statement. This database contains no $p proof statement.
$)

$c P2010B3I P2010B3Trans $.

p2010b3-index-syntax $a class P2010B3I $.
p2010b3-transition-syntax $a wff ( P2010B3Trans P T ) $.

p2010b3-index-definition $a |-
  P2010B3I = ( 0 ..^ ; ; ; 2 0 1 0 )
$.

${
  $d P T i j k t $.

  p2010b3-transition-definition $a |- (
    ( P2010B3Trans P T )
    <->
    A. t e. ( 0 ..^ T )
      E. i e. P2010B3I E. j e. P2010B3I
        (
          i =/= j
          /\
          (
            ( i + 1 ) <_ ( ( P ` t ) ` i )
            /\
            (
              ( ( P ` ( t + 1 ) ) ` i )
              =
              ( ( ( P ` t ) ` i ) - ( i + 1 ) )
              /\
              (
                ( ( P ` ( t + 1 ) ) ` j )
                =
                ( ( ( P ` t ) ` j ) + ( i + 1 ) )
                /\
                A. k e. P2010B3I
                  (
                    (
                      k =/= i
                      /\
                      k =/= j
                    )
                    ->
                    ( ( P ` ( t + 1 ) ) ` k )
                    =
                    ( ( P ` t ) ` k )
                  )
              )
            )
          )
        )
  ) $.
$}

${
  $d b i n p s $.

  putnambench-putnam-2010-b3 $a |- A. n e. NN
    (
      (
        A. b e. ( NN0 ^m P2010B3I )
          (
            (
              sum_ i e. P2010B3I ( b ` i )
            )
            =
            ( ; ; ; 2 0 1 0 x. n )
            ->
            E. p e. ( ( NN0 ^m P2010B3I ) ^m NN0 )
              E. s e. NN0
                (
                  ( p ` 0 ) = b
                  /\
                  (
                    ( P2010B3Trans p s )
                    /\
                    A. i e. P2010B3I
                      ( ( p ` s ) ` i ) = n
                  )
                )
          )
      )
      <->
      ; ; ; 1 0 0 5 <_ n
    )
  $.
$}
