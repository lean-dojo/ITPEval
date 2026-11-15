$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_b4: the alternating truncated sum of coefficients of powers
  of the integer polynomial 1 + x + x^2 lies between zero and one.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function a assigns to m and n the coefficient of x^n in
  (1 + x + x^2)^m.  The conclusion states the inclusive alternating sum
  through floor(2k/3) using integer arithmetic.
$)

${
  $d a i k m n $.

  putnambench-putnam-1997-b4 $a |-
    A. a e. ( ( ZZ ^m NN0 ) ^m NN0 )
      (
        A. m e. NN0
          A. n e. NN0
            ( ( a ` m ) ` n )
            =
            (
              ( coe1 `
                (
                  m
                  ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                  (
                    (
                      ( 1r ` ( Poly1 ` ZZring ) )
                      ( +g ` ( Poly1 ` ZZring ) )
                      ( var1 ` ZZring )
                    )
                    ( +g ` ( Poly1 ` ZZring ) )
                    (
                      2
                      ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                      ( var1 ` ZZring )
                    )
                  )
                )
              )
              ` n
            )
        ->
        A. k e. NN0
          (
            0
            <_
            (
              sum_ i e. ( 0 ... ( |_ ` ( ( 2 x. k ) / 3 ) ) )
                (
                  ( ( -u 1 ) ^ i )
                  x.
                  ( ( a ` ( k - i ) ) ` i )
                )
            )
            /\
            (
              (
                sum_ i e. ( 0 ... ( |_ ` ( ( 2 x. k ) / 3 ) ) )
                  (
                    ( ( -u 1 ) ^ i )
                    x.
                    ( ( a ` ( k - i ) ) ` i )
                  )
              )
              <_
              1
            )
          )
      )
  $.
$}
