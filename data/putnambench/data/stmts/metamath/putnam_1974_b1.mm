$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b1: maximizing the sum of all ten pairwise distances among
  five points on the unit circle is equivalent to a cyclic ordering with
  one positive common consecutive distance. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P74B1I is the two-coordinate index set, P74B1V is the five-element
  ordinal, and P74B1R2 is the real Euclidean plane. P74B1Succ is cyclic
  successor on the indices 0 through 4, and P74B1Dist is Euclidean distance.
  P74B1Unit says that every indexed point has distance one from the origin.
  P74B1Score is the sum over the ten pairs i < j, and P74B1Values is the set
  of all such scores for unit-circle configurations.

  P74B1Solution requires the five points to be distinct and retains the
  internally existential positive common distance and permutation from the
  source solution specification. Distinctness excludes repeated-vertex
  cycles with equal chord lengths, so the predicate describes a regular
  pentagon. Replacing Fin 5 by its five-element ordinal and expanding the
  definitionally specified objective function are bijective, definitional
  reindexings. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

$c P74B1I P74B1V P74B1R2 P74B1Zero P74B1Succ $.
$c P74B1Dist P74B1Unit P74B1Score P74B1Values P74B1Solution $.

p74b1-coordinate-index-syntax $a class P74B1I $.
p74b1-vertex-index-syntax $a class P74B1V $.
p74b1-plane-syntax $a class P74B1R2 $.
p74b1-zero-syntax $a class P74B1Zero $.
p74b1-successor-syntax $a class P74B1Succ $.
p74b1-distance-syntax $a class ( P74B1Dist A B ) $.
p74b1-unit-syntax $a wff ( P74B1Unit p ) $.
p74b1-score-syntax $a class ( P74B1Score p ) $.
p74b1-values-syntax $a class P74B1Values $.
p74b1-solution-syntax $a wff ( P74B1Solution p ) $.

p74b1-coordinate-index-definition $a |- P74B1I = ( 1 ... 2 ) $.

p74b1-vertex-index-definition $a |- P74B1V = 5 $.

p74b1-plane-definition $a |- P74B1R2 = ( RR ^m P74B1I ) $.

p74b1-zero-definition $a |- P74B1Zero =
  ( j e. P74B1I |-> 0 )
$.

p74b1-successor-definition $a |- P74B1Succ =
  (
    i e. P74B1V |->
      if (
        i = 4 ,
        0 ,
        ( i + 1 )
      )
  )
$.

${
  $d A B j $.

  p74b1-distance-definition $a |- (
    P74B1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P74B1I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d i p $.

  p74b1-unit-definition $a |- (
    ( P74B1Unit p )
    <->
    A. i e. P74B1V
      ( P74B1Dist ( p ` i ) P74B1Zero ) = 1
  ) $.
$}

${
  $d i j p $.

  p74b1-score-definition $a |- (
    P74B1Score p
  ) = (
    sum_ j e. P74B1V
      sum_ i e. { i e. P74B1V | i < j }
        ( P74B1Dist ( p ` i ) ( p ` j ) )
  ) $.
$}

${
  $d q r $.

  p74b1-values-definition $a |- P74B1Values = {
    r e. RR |
    E. q e. ( P74B1R2 ^m P74B1V )
      (
        ( P74B1Unit q )
        /\
        r = ( P74B1Score q )
      )
  } $.
$}

${
  $d B i o p $.

  p74b1-solution-definition $a |- (
    ( P74B1Solution p )
    <->
    (
      p : P74B1V -1-1-> P74B1R2
      /\
      E. B e. RR+
        E. o
          (
            o : P74B1V -1-1-onto-> P74B1V
            /\
            A. i e. P74B1V
              (
                P74B1Dist
                  ( p ` ( o ` i ) )
                  ( p ` ( o ` ( P74B1Succ ` i ) ) )
              )
              =
              B
          )
    )
  ) $.
$}

putnambench-putnam-1974-b1 $a |-
    A. p e. ( P74B1R2 ^m P74B1V )
      (
        ( P74B1Unit p )
        ->
        (
          (
            ( P74B1Score p )
            =
            sup ( P74B1Values , RR , < )
          )
          <->
          ( P74B1Solution p )
        )
      )
  $.
