$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_a5: for an odd prime p, the greatest nonnegative integer n
  such that (X - 1)^n divides the polynomial whose coefficient of X^k is
  k^((p - 1)/2) in the field of residues modulo p is (p - 1)/2.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For p prime, Z/nZ ` p is the field of residues modulo p and
  Poly1 ` ( Z/nZ ` p ) is its finite-support univariate polynomial ring.
  P19A5Q(p) is exactly the source sum from k = 1 through p - 1:
  ZRHom embeds the integer k^((p - 1)/2) into the residue field, algSc
  embeds that coefficient as a constant polynomial, and var1 is X.
  P19A5Factor(p) is the polynomial X - 1.

  The conclusion expands IsGreatest: the displayed exponent has the
  divisibility property, and every nonnegative exponent with that property
  is at most it. The two explicit definitions and final declaration are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P19A5Factor P19A5Q $.

p19a5-factor-syntax $a class ( P19A5Factor p ) $.
p19a5-q-syntax $a class ( P19A5Q p ) $.

p19a5-factor-definition $a |- ( P19A5Factor p ) =
  (
    ( var1 ` ( Z/nZ ` p ) )
    ( -g ` ( Poly1 ` ( Z/nZ ` p ) ) )
    (
      ( algSc ` ( Poly1 ` ( Z/nZ ` p ) ) )
      `
      ( 1r ` ( Z/nZ ` p ) )
    )
  )
$.

${
  $d k p $.

  p19a5-q-definition $a |- ( P19A5Q p ) =
    (
      ( Poly1 ` ( Z/nZ ` p ) )
      gsum
      (
        k e. ( 1 ... ( p - 1 ) ) |->
          (
            (
              ( algSc ` ( Poly1 ` ( Z/nZ ` p ) ) )
              `
              (
                ( ZRHom ` ( Z/nZ ` p ) )
                `
                ( k ^ ( ( p - 1 ) / 2 ) )
              )
            )
            ( .r ` ( Poly1 ` ( Z/nZ ` p ) ) )
            (
              k
              ( .g ` ( mulGrp ` ( Poly1 ` ( Z/nZ ` p ) ) ) )
              ( var1 ` ( Z/nZ ` p ) )
            )
          )
      )
    )
  $.
$}

${
  $d n p $.

  putnambench-putnam-2019-a5 $a |- A. p e. Prime
    (
      ( p mod 2 ) = 1
      ->
      (
        (
          (
            ( ( p - 1 ) / 2 )
            ( .g ` ( mulGrp ` ( Poly1 ` ( Z/nZ ` p ) ) ) )
            ( P19A5Factor p )
          )
          ( ||r ` ( Poly1 ` ( Z/nZ ` p ) ) )
          ( P19A5Q p )
        )
        /\
        A. n e. NN0
          (
            (
              (
                n
                ( .g ` ( mulGrp ` ( Poly1 ` ( Z/nZ ` p ) ) ) )
                ( P19A5Factor p )
              )
              ( ||r ` ( Poly1 ` ( Z/nZ ` p ) ) )
              ( P19A5Q p )
            )
            ->
            n <_ ( ( p - 1 ) / 2 )
          )
      )
    )
  $.
$}
