$(
  Statement-only formalization of Thousand Theorems corpus artifact Q570779
  (thousand-theorems__metamath__Q570779), "Vieta's formulas": over every
  commutative semiring, the product of the linear polynomials X + C(r) for a
  finite multiset equals the sum of monomials whose coefficients are its
  elementary symmetric sums. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A finite multiset is represented by an arbitrary finite sequence
  f : ( 1 ... n ) --> Base(R). Repeated sequence values retain multiplicity,
  and quotienting such sequences by permutation recovers finite multisets.
  Both sides below are invariant under permutation, so universal
  quantification over finite sequences is equivalent to universal
  quantification over finite multisets.

  Q570779Prod is the coefficient function of the product of X + C(f(i)).
  For coefficient k, a binary degree choice d selects either the constant
  coefficient f(i) or the degree-one coefficient 1 at every position, and
  the choices whose degrees sum to k are added in R.

  Q570779ESymm is the elementary symmetric sum of degree j, indexed by the
  j-element subsets of the sequence positions. Q570779Sum is the coefficient
  function of the sum from j = 0 through n of
  C(Q570779ESymm(R,n,f,j)) times X^(n-j). Equality of these coefficient
  functions is equality of the corresponding polynomials. Thus the final
  unproved $a assertion is bidirectionally equivalent to the Lean statement;
  all preceding $a declarations are syntax or transparent definitions, and
  this root statement file contains no $p proof declaration.
$)

$c Q570779Prod Q570779ESymm Q570779Sum $.

q570779-prod-syntax $a class ( Q570779Prod R n f ) $.
q570779-esymm-syntax $a class ( Q570779ESymm R n f j ) $.
q570779-sum-syntax $a class ( Q570779Sum R n f ) $.

${
  $d R d f i k n $.

  q570779-prod-definition $a |- ( Q570779Prod R n f ) =
    (
      k e. NN0 |->
        R gsum
          (
            d e.
              {
                d e. ( ( 0 ... 1 ) ^m ( 1 ... n ) ) |
                ( sum_ i e. ( 1 ... n ) ( d ` i ) ) = k
              }
            |->
              ( mulGrp ` R ) gsum
                (
                  i e. ( 1 ... n ) |->
                    if (
                      ( d ` i ) = 0
                      ,
                      ( f ` i )
                      ,
                      ( 1r ` R )
                    )
                )
          )
    )
  $.
$}

${
  $d R f i j n u $.

  q570779-esymm-definition $a |- ( Q570779ESymm R n f j ) =
    R gsum
      (
        u e.
          {
            u e. ~P ( 1 ... n ) |
            ( # ` u ) = j
          }
        |->
          ( mulGrp ` R ) gsum
            ( i e. u |-> ( f ` i ) )
      )
  $.
$}

${
  $d R f j k n $.

  q570779-sum-definition $a |- ( Q570779Sum R n f ) =
    (
      k e. NN0 |->
        R gsum
          (
            j e. ( 0 ... n ) |->
              if (
                k = ( n - j )
                ,
                ( Q570779ESymm R n f j )
                ,
                ( 0g ` R )
              )
          )
    )
  $.
$}

${
  $d R f n $.

  thousand-theorems-q570779-vieta-s-formulas $a |-
    A. R e. CSRing
      A. n e. NN0
        A. f e. ( ( Base ` R ) ^m ( 1 ... n ) )
          ( Q570779Prod R n f ) = ( Q570779Sum R n f )
  $.
$}
