$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_a6: a formal power series over a field of two elements,
  defined by even-length zero blocks in binary expansions, satisfies a
  cubic power-series identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P89A6Good is the set of nonnegative integers whose augmented little-endian
  binary digit list [1] ++ digits(2,n) ++ [1] has an even number of zeros
  between every pair of consecutive ones. For positive n, l is its exact
  binary length; for n = 0, l = 0. Positions 0 and l+1 are the two sentinel
  ones, while position i with 1 <= i <= l is the (i-1)-st binary digit.

  PwSer1 ` F is SetMM's complete univariate formal-power-series ring over the
  arbitrary field structure F, coe1 is its full NN0-indexed coefficient map,
  and var1 ` F is the series variable X. Thus the hypothesis defines every
  coefficient of alpha exactly as in the sources, and the conclusion is
  alpha^3 + X*alpha + 1 = 0 in that power-series ring. All declarations are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P89A6Good $.

p89a6-good-syntax $a class P89A6Good $.

${
  $d i j k l n $.

  p89a6-good-definition $a |- P89A6Good =
    {
      n e. NN0 |
      E. l e. NN0
        (
          (
            (
              n = 0
              /\
              l = 0
            )
            \/
            (
              n e. NN
              /\
              (
                ( 2 ^ ( l - 1 ) ) <_ n
                /\
                n < ( 2 ^ l )
              )
            )
          )
          /\
          A. i e. ( 0 ... ( l + 1 ) )
            A. j e. ( 0 ... ( l + 1 ) )
              (
                (
                  i < j
                  /\
                  (
                    (
                      i = 0
                      \/
                      i = ( l + 1 )
                    )
                    \/
                    (
                      ( ( |_ ` ( n / ( 2 ^ ( i - 1 ) ) ) ) mod 2 )
                      =
                      1
                    )
                  )
                )
                /\
                (
                  (
                    (
                      j = 0
                      \/
                      j = ( l + 1 )
                    )
                    \/
                    (
                      ( ( |_ ` ( n / ( 2 ^ ( j - 1 ) ) ) ) mod 2 )
                      =
                      1
                    )
                  )
                  /\
                  A. k e. ( 0 ... ( l + 1 ) )
                    (
                      (
                        i < k
                        /\
                        k < j
                      )
                      ->
                      (
                        ( ( |_ ` ( n / ( 2 ^ ( k - 1 ) ) ) ) mod 2 )
                        =
                        0
                      )
                    )
                )
                ->
                2 || ( ( j - i ) - 1 )
              )
        )
    }
  $.
$}

${
  $d F a n $.

  putnambench-putnam-1989-a6 $a |-
    A. F
      A. a e. ( Base ` ( PwSer1 ` F ) )
        (
          (
            (
              F e. Field
              /\
              (
                ( Base ` F ) e. Fin
                /\
                ( # ` ( Base ` F ) ) = 2
              )
            )
            /\
            A. n e. NN0
              ( ( coe1 ` a ) ` n )
              =
              if (
                n e. P89A6Good ,
                ( 1r ` F ) ,
                ( 0g ` F )
              )
          )
          ->
          (
            (
              (
                3
                ( .g ` ( mulGrp ` ( PwSer1 ` F ) ) )
                a
              )
              ( +g ` ( PwSer1 ` F ) )
              (
                ( var1 ` F )
                ( .r ` ( PwSer1 ` F ) )
                a
              )
            )
            ( +g ` ( PwSer1 ` F ) )
            ( 1r ` ( PwSer1 ` F ) )
          )
          =
          ( 0g ` ( PwSer1 ` F ) )
        )
  $.
$}
