$(
  Statement-only formalization of Thousand Theorems corpus artifact Q472883
  (thousand-theorems__metamath__Q472883), "Quadratic reciprocity theorem":
  the Legendre reciprocity law for distinct odd primes and the Jacobi
  reciprocity law for arbitrary odd natural numbers. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's /L is the integer-valued Kronecker symbol. Its restriction to an odd
  prime denominator is the Legendre symbol, and its restriction to a positive
  odd denominator is the Jacobi symbol. Thus the two assertions below encode
  the indexed Lean declarations legendreSym.quadratic_reciprocity and
  jacobiSym.quadratic_reciprocity.

  Prime \ { 2 } gives exactly the Legendre theorem's odd-prime assumptions.
  The Jacobi theorem ranges over NN and assumes only membership in Odd; it
  has no primality, distinctness, or coprimality assumption. For every
  positive odd natural n, Lean's natural quotient n / 2 equals the integer
  ( n - 1 ) / 2 used in the SetMM exponents.

  The final declarations are the two unproved corpus $a statements. This
  root artifact contains no $p proof statement.
$)

${
  $d p q $.

  thousand-theorems-q472883-quadratic-reciprocity $a |- (
    A. p e. ( Prime \ { 2 } )
      A. q e. ( Prime \ { 2 } )
        (
          p =/= q
          ->
          (
            ( ( q /L p ) x. ( p /L q ) )
            =
            (
              -u 1
              ^
              (
                ( ( p - 1 ) / 2 )
                x.
                ( ( q - 1 ) / 2 )
              )
            )
          )
        )
  ) $.
$}

${
  $d a b $.

  thousand-theorems-q472883-jacobi-quadratic-reciprocity $a |- (
    A. a e. NN
      A. b e. NN
        (
          (
            a e. Odd
            /\
            b e. Odd
          )
          ->
          (
            ( a /L b )
            =
            (
              (
                -u 1
                ^
                (
                  ( ( a - 1 ) / 2 )
                  x.
                  ( ( b - 1 ) / 2 )
                )
              )
              x.
              ( b /L a )
            )
          )
        )
  ) $.
$}
