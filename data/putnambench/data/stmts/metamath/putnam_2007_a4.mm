$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_a4: classification of the real polynomials that map every
  base-ten repunit to a base-ten repunit. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P07A4Repunit is the set of positive integers whose base-ten digits are all
  one: every such number, and only such a number, is a finite sum
  1 + 10 + ... + 10^m for a nonnegative integer m.

  Poly ` RR is set.mm's class of polynomial functions with real
  coefficients. The biconditional states the full classification from the
  ground truth: p preserves repunits exactly when there are d in NN0 and c
  in ZZ with c >= 1 - d such that, on every real x,

                 p(x) = (10^c (9x + 1)^d - 1) / 9.

  Thus the polynomial, real domain, universal repunit condition, and both
  internal classification witnesses are preserved. The declarations are
  unproved $a statement encodings; this database contains no $p proof
  statement.
$)

$c P07A4Repunit $.

p07a4-repunit-syntax $a class P07A4Repunit $.

${
  $d i m n $.

  p07a4-repunit-definition $a |- P07A4Repunit =
    {
      n e. NN |
        E. m e. NN0
          n =
          sum_ i e. ( 0 ... m )
            ( ; 1 0 ^ i )
    }
  $.
$}

${
  $d c d n p x $.

  putnambench-putnam-2007-a4 $a |-
    A. p e. ( Poly ` RR )
      (
        A. n e. P07A4Repunit
          ( p ` n ) e. P07A4Repunit
        <->
        E. d e. NN0 E. c e. ZZ
          (
            ( 1 - d ) <_ c
            /\
            A. x e. RR
              ( p ` x )
              =
              (
                (
                  (
                    ( ; 1 0 ^ c )
                    x.
                    ( ( ( 9 x. x ) + 1 ) ^ d )
                  )
                  -
                  1
                )
                /
                9
              )
          )
      )
  $.
$}
