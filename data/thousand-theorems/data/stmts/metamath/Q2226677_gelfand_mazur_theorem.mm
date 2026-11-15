$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2226677
  (thousand-theorems__metamath__Q2226677), "Gelfand-Mazur theorem": a complete
  complex normed algebra in which the units are exactly the nonzero elements
  is algebra-equivalent to the complex numbers. The conclusion uses the
  equivalent target-native statement that the canonical complex scalar map is
  a bijection. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's native NrmRing requires a multiplicative norm, which is stronger
  than Lean's NormedRing. Q2226677NormedRing instead combines the ring and
  normed-additive-group structures with precisely the source inequality
  norm(x * y) <= norm(x) * norm(y); no normalization of norm(1) is assumed.

  Membership in NrmMod and AssAlg supplies the compatible complex normed
  module and associative-algebra structures, while CMetSp supplies
  completeness. Since algSc is the canonical algebra homomorphism, its being
  one-to-one and onto is equivalent to the source algebra equivalence.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax or a faithful definition, and this
  database contains no $p proof statement.
$)

$c Q2226677NormedRing $.

q2226677-normed-ring-syntax $a
  wff ( Q2226677NormedRing A ) $.

${
  $d A x y $.

  q2226677-normed-ring-definition $a
    |- ( ( Q2226677NormedRing A ) <->
         ( A e. ( Ring i^i NrmGrp ) /\
           A. x e. ( Base ` A ) A. y e. ( Base ` A )
             ( ( ( norm ` A ) ` ( x ( .r ` A ) y ) ) <_
               ( ( ( norm ` A ) ` x ) x.
                 ( ( norm ` A ) ` y ) ) ) ) ) ) $.
$}

${
  $d A a $.

  q2226677-gelfand-mazur $a
    |- A. A
         ( ( ( Q2226677NormedRing A ) /\
             ( A e. ( ( NrmMod i^i AssAlg ) i^i CMetSp ) /\
               ( ( Scalar ` A ) = CCfld /\
                 A. a e. ( Base ` A )
                   ( a e. ( Unit ` A ) <->
                     a =/= ( 0g ` A ) ) ) ) ) )
           ->
           ( ( algSc ` A ) :
             ( Base ` CCfld ) -1-1-onto-> ( Base ` A ) ) ) $.
$}
