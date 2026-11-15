$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b4: for the integer matrix with rows (3,2) and (4,3),
  the gcd of the four entries of its nth power minus the identity matrix
  tends to positive infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The structure ( ( 0 ..^ 2 ) Mat ZZring ) is the full ring of 2 by 2
  integer matrices, indexed by { 0, 1 }. P94B4A is the fixed matrix from
  the source statements. The mulGrp exponent is matrix-ring exponentiation,
  so exponent zero gives the identity matrix.

  P94B4D takes the nested integer gcd of the four entries after subtracting
  the identity entries 1, 0, 0, 1. Integer gcd values lie in NN0. The final
  assertion expands convergence to positive infinity as: every natural
  bound k is eventually a lower bound for P94B4D. All declarations below
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P94B4A P94B4D $.

p94b4-a-syntax $a class P94B4A $.
p94b4-d-syntax $a class P94B4D $.

${
  $d i j $.

  p94b4-a-definition $a |- P94B4A =
    (
      i e. ( 0 ..^ 2 ) , j e. ( 0 ..^ 2 ) |->
        if
        (
          i = 0 ,
          if ( j = 0 , 3 , 2 ) ,
          if ( j = 0 , 4 , 3 )
        )
    ) $.
$}

p94b4-d-definition $a |- P94B4D =
  (
    n e. NN0 |->
      (
        (
          (
            (
              (
                n
                ( .g ` ( mulGrp ` ( ( 0 ..^ 2 ) Mat ZZring ) ) )
                P94B4A
              )
              ` <. 0 , 0 >.
            )
            - 1
          )
          gcd
          (
            (
              n
              ( .g ` ( mulGrp ` ( ( 0 ..^ 2 ) Mat ZZring ) ) )
              P94B4A
            )
            ` <. 0 , 1 >.
          )
        )
        gcd
        (
          (
            n
            ( .g ` ( mulGrp ` ( ( 0 ..^ 2 ) Mat ZZring ) ) )
            P94B4A
          )
          ` <. 1 , 0 >.
        )
      )
      gcd
      (
        (
          (
            n
            ( .g ` ( mulGrp ` ( ( 0 ..^ 2 ) Mat ZZring ) ) )
            P94B4A
          )
          ` <. 1 , 1 >.
        )
        - 1
      )
  ) $.

${
  $d k N n $.

  putnambench-putnam-1994-b4 $a |-
    A. k e. NN0
      E. N e. NN0
        A. n e. NN0
          ( N <_ n -> k <_ ( P94B4D ` n ) )
  $.
$}
