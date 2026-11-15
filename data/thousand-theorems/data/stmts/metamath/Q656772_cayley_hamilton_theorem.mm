$(
  Statement-only formalization of Thousand Theorems corpus artifact Q656772
  (thousand-theorems__metamath__Q656772), "Cayley-Hamilton theorem": over every
  commutative ring, each square matrix on an arbitrary finite index carrier
  evaluates its characteristic polynomial to the zero matrix. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For a finite carrier N and commutative ring R, ( N CharPlyMat R ) maps a
  square matrix M to det(tI - M).  The coefficient function coe1, scalar
  multiplication in ( N Mat R ), powers in its multiplicative monoid, and
  gsum together give the usual polynomial evaluation at M.

  The following $a is the single unproved corpus statement.  This artifact
  adds no $p assertion.
$)

${
  $d M N R n $.
  thousand-theorems-q656772-cayley-hamilton-theorem $a |- A. R e. CRing
    A. N e. Fin
    A. M e. ( Base ` ( N Mat R ) )
      ( ( N Mat R ) gsum
          ( n e. NN0 |->
            ( ( ( coe1 ` ( ( N CharPlyMat R ) ` M ) ) ` n )
              ( .s ` ( N Mat R ) )
              ( n ( .g ` ( mulGrp ` ( N Mat R ) ) ) M ) ) ) )
        = ( 0g ` ( N Mat R ) ) ) $.
$}
