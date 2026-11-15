$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_b6: modulo a prime, the determinant of the three-by-three
  matrix whose rows are the p-power iterates of three variables is a finite
  product of integer linear forms in those variables. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P02B6Poly is SetMM's ring of finite-support polynomials over ZZ in the
  three variables indexed by the integer interval 0 ... 2, and P02B6Vars is
  its canonical variable
  map. P02B6Matrix p has entry X_c^(p^r), with ring exponentiation in
  P02B6Poly, so P02B6Det p is exactly the source determinant.

  P02B6Lin a b c is the polynomial ax + by + cz, with integer constants
  embedded into the polynomial ring. P02B6Prod S is the finite
  multiplicative product of the polynomial set S. P02B6Cong compares the
  coefficient functions at every exponent vector in NN0 ^m (0 ... 2), using
  equality of integer remainders modulo p. Thus it is exactly
  coefficientwise polynomial congruence modulo p.

  The finite-set witness and all integer coefficients remain existentially
  quantified inside the quantifier over the prime. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

$c P02B6Poly P02B6Vars P02B6Matrix P02B6Det P02B6Lin P02B6Prod
   P02B6Cong $.

p02b6-poly-syntax $a class P02B6Poly $.
p02b6-vars-syntax $a class P02B6Vars $.
p02b6-matrix-syntax $a class ( P02B6Matrix p ) $.
p02b6-det-syntax $a class ( P02B6Det p ) $.
p02b6-lin-syntax $a class ( P02B6Lin a b c ) $.
p02b6-prod-syntax $a class ( P02B6Prod S ) $.
p02b6-cong-syntax $a wff ( P02B6Cong p F G ) $.

p02b6-poly-definition $a |- P02B6Poly =
  ( ( 0 ... 2 ) mPoly ZZring ) $.

p02b6-vars-definition $a |- P02B6Vars =
  ( ( 0 ... 2 ) mVar ZZring ) $.

${
  $d c p r $.

  p02b6-matrix-definition $a |- ( P02B6Matrix p ) =
    (
      r e. ( 0 ... 2 ) , c e. ( 0 ... 2 ) |->
        (
          ( p ^ r )
          ( .g ` ( mulGrp ` P02B6Poly ) )
          ( P02B6Vars ` c )
        )
    ) $.
$}

p02b6-det-definition $a |- ( P02B6Det p ) =
  ( ( ( 0 ... 2 ) maDet P02B6Poly ) ` ( P02B6Matrix p ) ) $.

${
  $d a b c $.

  p02b6-lin-definition $a |- ( P02B6Lin a b c ) =
    (
      (
        (
          ( ( algSc ` P02B6Poly ) ` a )
          ( .r ` P02B6Poly )
          ( P02B6Vars ` 0 )
        )
        ( +g ` P02B6Poly )
        (
          ( ( algSc ` P02B6Poly ) ` b )
          ( .r ` P02B6Poly )
          ( P02B6Vars ` 1 )
        )
      )
      ( +g ` P02B6Poly )
      (
        ( ( algSc ` P02B6Poly ) ` c )
        ( .r ` P02B6Poly )
        ( P02B6Vars ` 2 )
      )
    ) $.
$}

${
  $d S s $.

  p02b6-prod-definition $a |- ( P02B6Prod S ) =
    (
      ( mulGrp ` P02B6Poly )
      gsum
      ( s e. S |-> s )
    ) $.
$}

${
  $d F G n p $.

  p02b6-cong-definition $a |- (
    ( P02B6Cong p F G )
    <->
    A. n e. ( NN0 ^m ( 0 ... 2 ) )
      ( ( F ` n ) mod p ) = ( ( G ` n ) mod p )
  ) $.
$}

${
  $d a b c p u v $.

  putnambench-putnam-2002-b6 $a |-
    A. p e. Prime
      E. u e. Fin
        (
          u C_ ( Base ` P02B6Poly )
          /\
          (
            A. v e. u
              E. a e. ZZ E. b e. ZZ E. c e. ZZ
                v = ( P02B6Lin a b c )
            /\
            ( P02B6Cong p ( P02B6Det p ) ( P02B6Prod u ) )
          )
        )
  $.
$}
