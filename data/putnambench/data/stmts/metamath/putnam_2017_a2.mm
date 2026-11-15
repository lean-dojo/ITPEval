$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_a2: the rational-function sequence beginning with 1 and X and
  satisfying the stated nonlinear recurrence has integer-coefficient
  polynomial terms at every positive index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P17A2QFld is Set.mm's rational subfield of the complex field. P17A2QPoly and
  P17A2ZPoly are its univariate polynomial ring and the univariate polynomial
  ring over the integers. P17A2RatFunc is the field of fractions of
  P17A2QPoly, hence the rational-function field over QQ. P17A2Embed is the
  canonical embedding p |-> p/1 into that field.

  The recurrence uses the native subtraction and total division operations of
  P17A2RatFunc, so it also agrees with the source field semantics when a
  divisor is zero. In the conclusion, P is an integer polynomial and p is its
  coefficientwise image under the canonical integer-to-rational homomorphism;
  Q(n) is then the embedded rational polynomial p. Thus the internal
  integer-polynomial witness and the arbitrary rational-function domain are
  both preserved.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof statement.
$)

$c P17A2QFld P17A2QPoly P17A2ZPoly P17A2RatFunc P17A2Embed $.

p17a2-qfld-syntax $a class P17A2QFld $.
p17a2-qpoly-syntax $a class P17A2QPoly $.
p17a2-zpoly-syntax $a class P17A2ZPoly $.
p17a2-ratfunc-syntax $a class P17A2RatFunc $.
p17a2-embed-syntax $a class P17A2Embed $.

p17a2-qfld-definition $a |-
  P17A2QFld = ( CCfld |`s QQ ) $.

p17a2-qpoly-definition $a |-
  P17A2QPoly = ( Poly1 ` P17A2QFld ) $.

p17a2-zpoly-definition $a |-
  P17A2ZPoly = ( Poly1 ` ZZring ) $.

p17a2-ratfunc-definition $a |-
  P17A2RatFunc = ( Frac ` P17A2QPoly ) $.

${
  p17a2-embed-definition $a |- P17A2Embed =
    (
      p e. ( Base ` P17A2QPoly ) |->
        [
          <. p , ( 1r ` P17A2QPoly ) >.
        ]
        ( P17A2QPoly ~RL ( RLReg ` P17A2QPoly ) )
    ) $.
$}

${
  $d P Q k n p $.

  putnambench-putnam-2017-a2 $a |-
    A. Q e. ( ( Base ` P17A2RatFunc ) ^m NN0 )
      (
        (
          (
            ( Q ` 0 )
            =
            ( P17A2Embed ` ( 1r ` P17A2QPoly ) )
            /\
            ( Q ` 1 )
            =
            ( P17A2Embed ` ( var1 ` P17A2QFld ) )
          )
          /\
          A. n e. NN0
            ( Q ` ( n + 2 ) )
            =
            (
              (
                (
                  ( Q ` ( n + 1 ) )
                  ( .r ` P17A2RatFunc )
                  ( Q ` ( n + 1 ) )
                )
                ( -g ` P17A2RatFunc )
                ( 1r ` P17A2RatFunc )
              )
              ( /r ` P17A2RatFunc )
              ( Q ` n )
            )
        )
        ->
        A. n e. NN
          E. P e. ( Base ` P17A2ZPoly )
            E. p e. ( Base ` P17A2QPoly )
              (
                A. k e. NN0
                  (
                    ( ( coe1 ` p ) ` k )
                    =
                    (
                      ( ZRHom ` P17A2QFld )
                      `
                      ( ( coe1 ` P ) ` k )
                    )
                  )
                /\
                ( Q ` n ) = ( P17A2Embed ` p )
              )
      )
  $.
$}
