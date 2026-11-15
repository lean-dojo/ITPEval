$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_b3: not every positive irrational real triple with coordinate
  sum one becomes balanced after finitely many iterations of the specified
  coordinatewise doubling map. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P77B3R3 is the set of real ordered triples, represented by set.mm's nested
  pairs <. <. a , b >. , c >.  P77B3Admissible is the source predicate P:
  all three coordinates are positive and irrational and have sum one.
  P77B3Balanced requires all three coordinates to be strictly below one half.

  P77B3Step is exactly the source map B. IterComp is set.mm's native
  finite-iteration operator, so ((IterComp ` P77B3Step) ` n) ` t is B
  iterated n times at t, including the identity iterate at n = 0.

  The ground-truth solution is False. Therefore the final unproved $a
  assertion is the negation of the universal eventual-balancing proposition,
  which is logically equivalent to that proposition being equivalent to
  False. This database contains no $p proof statement.
$)

$c P77B3R3 P77B3Admissible P77B3Balanced P77B3Step $.

p77b3-space-syntax $a class P77B3R3 $.
p77b3-admissible-syntax $a wff ( P77B3Admissible t ) $.
p77b3-balanced-syntax $a wff ( P77B3Balanced A ) $.
p77b3-step-syntax $a class P77B3Step $.

p77b3-space-definition $a |- P77B3R3 = ( ( RR X. RR ) X. RR ) $.

p77b3-admissible-definition $a |- (
  ( P77B3Admissible t )
  <->
  (
    ( 1st ` ( 1st ` t ) ) e/ QQ
    /\
    (
      ( 2nd ` ( 1st ` t ) ) e/ QQ
      /\
      (
        ( 2nd ` t ) e/ QQ
        /\
        (
          0 < ( 1st ` ( 1st ` t ) )
          /\
          (
            0 < ( 2nd ` ( 1st ` t ) )
            /\
            (
              0 < ( 2nd ` t )
              /\
              (
                (
                  ( 1st ` ( 1st ` t ) )
                  +
                  ( 2nd ` ( 1st ` t ) )
                )
                +
                ( 2nd ` t )
              )
              =
              1
            )
          )
        )
      )
    )
  )
) $.

p77b3-balanced-definition $a |- (
  ( P77B3Balanced A )
  <->
  (
    ( 1st ` ( 1st ` A ) ) < ( 1 / 2 )
    /\
    (
      ( 2nd ` ( 1st ` A ) ) < ( 1 / 2 )
      /\
      ( 2nd ` A ) < ( 1 / 2 )
    )
  )
) $.

p77b3-step-definition $a |- P77B3Step = (
  t e. P77B3R3 |->
    <.
      <.
        if (
          ( 1 / 2 ) < ( 1st ` ( 1st ` t ) ) ,
          ( ( 2 x. ( 1st ` ( 1st ` t ) ) ) - 1 ) ,
          ( 2 x. ( 1st ` ( 1st ` t ) ) )
        )
        ,
        if (
          ( 1 / 2 ) < ( 2nd ` ( 1st ` t ) ) ,
          ( ( 2 x. ( 2nd ` ( 1st ` t ) ) ) - 1 ) ,
          ( 2 x. ( 2nd ` ( 1st ` t ) ) )
        )
      >.
      ,
      if (
        ( 1 / 2 ) < ( 2nd ` t ) ,
        ( ( 2 x. ( 2nd ` t ) ) - 1 ) ,
        ( 2 x. ( 2nd ` t ) )
      )
    >.
) $.

${
  $d n t $.

  putnambench-putnam-1977-b3 $a |- -.
    A. t e. P77B3R3
      (
        ( P77B3Admissible t )
        ->
        E. n e. NN0
          (
            P77B3Balanced
              (
                ( ( IterComp ` P77B3Step ) ` n )
                `
                t
              )
          )
      )
  $.
$}
