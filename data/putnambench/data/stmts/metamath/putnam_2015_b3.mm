$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b3: classification of real 2 by 2 arithmetic-progression
  matrices having a higher power with the same property. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ((0 ..^ 2) Mat RRfld) is the full real 2 by 2 matrix ring.
  P15B3AP expresses that the four entries, read row by row, form an
  arithmetic progression. P15B3Sol is the solution union from the primary
  Lean source: constant matrices, or scalar multiples of the matrix with
  rows (-3,-1) and (1,3).

  The multiplicative-group operation gives ordinary natural matrix powers.
  Inlining the source equality defining S yields the left side of the final
  biconditional, so omitting S is a bidirectionally equivalent definitional
  substitution. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

$c P15B3AP P15B3Sol $.

p15b3-ap-syntax $a wff ( P15B3AP A ) $.
p15b3-solution-syntax $a wff ( P15B3Sol A ) $.

p15b3-ap-definition $a |- (
  ( P15B3AP A )
  <->
  (
    (
      ( A ` <. 0 , 1 >. )
      -
      ( A ` <. 0 , 0 >. )
    )
    =
    (
      ( A ` <. 1 , 0 >. )
      -
      ( A ` <. 0 , 1 >. )
    )
    /\
    (
      (
        ( A ` <. 1 , 0 >. )
        -
        ( A ` <. 0 , 1 >. )
      )
      =
      (
        ( A ` <. 1 , 1 >. )
        -
        ( A ` <. 1 , 0 >. )
      )
    )
  )
) $.

${
  $d A a b $.

  p15b3-solution-definition $a |- (
    ( P15B3Sol A )
    <->
    (
      E. a e. RR
        (
          (
            ( A ` <. 0 , 0 >. ) = ( a x. 1 )
            /\
            ( A ` <. 0 , 1 >. ) = ( a x. 1 )
          )
          /\
          (
            ( A ` <. 1 , 0 >. ) = ( a x. 1 )
            /\
            ( A ` <. 1 , 1 >. ) = ( a x. 1 )
          )
        )
      \/
      E. b e. RR
        (
          (
            ( A ` <. 0 , 0 >. ) = ( b x. ( -u 3 ) )
            /\
            ( A ` <. 0 , 1 >. ) = ( b x. ( -u 1 ) )
          )
          /\
          (
            ( A ` <. 1 , 0 >. ) = ( b x. 1 )
            /\
            ( A ` <. 1 , 1 >. ) = ( b x. 3 )
          )
        )
    )
  ) $.
$}

${
  $d A k $.

  putnambench-putnam-2015-b3 $a |-
    A. A e. ( Base ` ( ( 0 ..^ 2 ) Mat RRfld ) )
      (
        (
          ( P15B3AP A )
          /\
          E. k e. NN0
            (
              1 < k
              /\
              (
                P15B3AP
                (
                  k
                  ( .g ` ( mulGrp ` ( ( 0 ..^ 2 ) Mat RRfld ) ) )
                  A
                )
              )
            )
        )
        <->
        ( P15B3Sol A )
      )
  $.
$}
