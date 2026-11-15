$(
  Statement-only formalization of Thousand Theorems corpus artifact Q657482
  (thousand-theorems__metamath__Q657482), "Abel-Ruffini theorem": there
  exists a complex number algebraic over the rationals that is not obtainable
  by radicals over the rationals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q657482RadClosure is the intersection of all subsets s of CC that contain
  QQ, are closed under the field operations, and contain every complex n-th
  root of each of their elements for every positive integer n. It is thus the
  least intermediate field between QQ and CC closed under radicals, matching
  solvableByRad QQ CC in the Lean source.

  SetMM's AA is the class of complex numbers algebraic over QQ. Therefore the
  final assertion directly preserves the source existential quantifier,
  complex domain, algebraicity conjunct, and non-membership in the radical
  closure. The declarations are unproved $a statements; this file contains no
  $p proof statement.
$)

$c Q657482RadClosure $.

cq657482radclosure $a class Q657482RadClosure $.

${
  $d a b n s z $.

  df-q657482radclosure $a |- Q657482RadClosure =
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

thousand-theorems-q657482-abel-ruffini $a |- E. z e. CC
  (
    z e. AA
    /\
    z e/ Q657482RadClosure
  ) $.
