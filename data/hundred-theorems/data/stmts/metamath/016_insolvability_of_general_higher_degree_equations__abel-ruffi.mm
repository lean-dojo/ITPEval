$(
  Statement-only formalization of "Insolvability of General Higher Degree
  Equations (Abel-Ruffini)" from Hundred Theorems item 016: an algebraic
  complex root of x^5 - 4x + 2 is not obtainable by radicals over the
  rationals. This file contains no proof.
$)

$[ library/set.mm $]

$(
  HundredRadClosure016 is the intersection of all subsets s of CC that
  contain QQ, are closed under the field operations, and contain every
  complex n-th root of each of their elements for every positive integer n.
  It is therefore the least intermediate field between QQ and CC closed
  under radicals, matching solvableByRad QQ CC in the Lean source and the
  finite radical-tower formulation in the Rocq source.

  The class AA is the set.mm class of complex numbers algebraic over QQ.
  The final assertion gives the explicit quintic witness used by both source
  developments. The declarations are unproved $a statements, following the
  corpus convention for Metamath statement artifacts; there is no $p proof
  statement in this file.
$)

$c HundredRadClosure016 $.

chundredradclosure016 $a class HundredRadClosure016 $.

${
  $d a b n s z $.

  df-hundredradclosure016 $a |- HundredRadClosure016 =
    { z e. CC | A. s
      (
        (
          (
            (
              s C_ CC
              /\
              QQ C_ s
            )
            /\
            A. a e. s A. b e. s
            (
              (
                ( a + b ) e. s
                /\
                ( a - b ) e. s
              )
              /\
              (
                ( a x. b ) e. s
                /\
                ( b =/= 0 -> ( a / b ) e. s )
              )
            )
          )
          /\
          A. a e. CC A. n e. NN
            ( ( a ^ n ) e. s -> a e. s )
        )
        ->
        z e. s
      )
    } $.
$}

hundred-theorems-016-abel-ruffini $a |- E. z e. CC
  (
    z e. AA
    /\
    (
      ( ( ( z ^ 5 ) - ( 4 x. z ) ) + 2 ) = 0
      /\
      z e/ HundredRadClosure016
    )
  ) $.
