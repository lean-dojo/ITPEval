$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b4: existence, for every natural exponent n greater than one,
  of an integer-coefficient polynomial in three variables that
  recovers each integer x from x^n, x^(n+1), and x+x^(n+2).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 3o is the three-element variable-index set. Thus
  ( 3o mPoly ZZring ) is set.mm's ring of finite-support polynomials in
  three variables over the integers, and ( 3o eval ZZring ) evaluates such
  a polynomial at an assignment from 3o to ZZ. The assignment sends ordinal
  indices (/), 1o, and 2o respectively to x^n, x^(n+1), and x+x^(n+2).

  The polynomial witness remains existentially quantified inside the
  universal quantifier over n. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d i n p x $.

  putnambench-putnam-1972-b4 $a |-
    A. n e. NN0
      (
        1 < n
        ->
        E. p e. ( Base ` ( 3o mPoly ZZring ) )
          A. x e. ZZ
            x
            =
            (
              ( ( 3o eval ZZring ) ` p )
              `
              (
                i e. 3o |->
                  if (
                    i = (/) ,
                    ( x ^ n ) ,
                    if (
                      i = 1o ,
                      ( x ^ ( n + 1 ) ) ,
                      ( x + ( x ^ ( n + 2 ) ) )
                    )
                  )
              )
            )
      )
  $.
$}
