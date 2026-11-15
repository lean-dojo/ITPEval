$(
  Statement-only formalization of the Babel-formal inner_product artifact:
  negation, sum, difference, orthogonality, and parallelogram identities for
  an abstract symmetric bilinear inner product. This file contains no proof.
$)

$(
  Statement-only encoding of an abstract scalar field, vector space, and
  symmetric bilinear inner product.

  The scalar-field, vector-space, subtraction, and inner-product laws form the
  global context of this Metamath database. Variables in those laws and in the
  translated results are schematic, preserving universal quantification over
  arbitrary scalar and vector elements. Every mathematical declaration and
  result is an unproved $a assertion; this database contains no proof
  statements.
$)

$c
  scalar vector wff |-
  ( )
  zeroR oneR addR mulR oppR
  zeroV addV oppV smul subV ip
  =R =V
$.

$v a b c x y z u v w $.

ra $f scalar a $.
rb $f scalar b $.
rc $f scalar c $.
rx $f scalar x $.
ry $f scalar y $.
rz $f scalar z $.

vu $f vector u $.
vv $f vector v $.
vw $f vector w $.

zero-r-term $a scalar zeroR $.
one-r-term $a scalar oneR $.
add-r-term $a scalar ( addR x y ) $.
mul-r-term $a scalar ( mulR x y ) $.
opp-r-term $a scalar ( oppR x ) $.

zero-v-term $a vector zeroV $.
add-v-term $a vector ( addV u v ) $.
opp-v-term $a vector ( oppV u ) $.
smul-term $a vector ( smul a u ) $.
sub-v-term $a vector ( subV u v ) $.
ip-term $a scalar ( ip u v ) $.

eq-r-formula $a wff ( x =R y ) $.
eq-v-formula $a wff ( u =V v ) $.

$(
  Scalar-field laws in the global context.
$)
add-r-comm $a |- (
  ( addR x y ) =R ( addR y x )
) $.

add-r-assoc $a |- (
  ( addR ( addR x y ) z ) =R ( addR x ( addR y z ) )
) $.

add-r-zero $a |- (
  ( addR x zeroR ) =R x
) $.

zero-r-add $a |- (
  ( addR zeroR x ) =R x
) $.

add-r-opp $a |- (
  ( addR x ( oppR x ) ) =R zeroR
) $.

mul-r-comm $a |- (
  ( mulR x y ) =R ( mulR y x )
) $.

mul-r-assoc $a |- (
  ( mulR ( mulR x y ) z ) =R ( mulR x ( mulR y z ) )
) $.

mul-r-one $a |- (
  ( mulR x oneR ) =R x
) $.

dist-r-left $a |- (
  ( mulR x ( addR y z ) )
  =R
  ( addR ( mulR x y ) ( mulR x z ) )
) $.

opp-r-add $a |- (
  ( oppR ( addR x y ) ) =R ( addR ( oppR x ) ( oppR y ) )
) $.

mul-r-opp-one $a |- (
  ( mulR ( oppR oneR ) x ) =R ( oppR x )
) $.

opp-r-opp $a |- (
  ( oppR ( oppR x ) ) =R x
) $.

$(
  Vector-space and subtraction laws in the global context.
$)
add-v-comm $a |- (
  ( addV u v ) =V ( addV v u )
) $.

add-v-assoc $a |- (
  ( addV ( addV u v ) w ) =V ( addV u ( addV v w ) )
) $.

add-v-zero $a |- (
  ( addV u zeroV ) =V u
) $.

add-v-opp $a |- (
  ( addV u ( oppV u ) ) =V zeroV
) $.

smul-add-v $a |- (
  ( smul a ( addV u v ) )
  =V
  ( addV ( smul a u ) ( smul a v ) )
) $.

add-r-smul $a |- (
  ( smul ( addR a b ) u )
  =V
  ( addV ( smul a u ) ( smul b u ) )
) $.

mul-r-smul $a |- (
  ( smul ( mulR a b ) u ) =V ( smul a ( smul b u ) )
) $.

one-r-smul $a |- (
  ( smul oneR u ) =V u
) $.

smul-zero-v $a |- (
  ( smul a zeroV ) =V zeroV
) $.

opp-v-smul-one $a |- (
  ( oppV u ) =V ( smul ( oppR oneR ) u )
) $.

sub-v-def $a |- (
  ( subV u v ) =V ( addV u ( oppV v ) )
) $.

$(
  Symmetric bilinear inner-product laws in the global context.
$)
ip-linear-left-add $a |- (
  ( ip ( addV u v ) w )
  =R
  ( addR ( ip u w ) ( ip v w ) )
) $.

ip-linear-left-smul $a |- (
  ( ip ( smul a u ) v ) =R ( mulR a ( ip u v ) )
) $.

ip-linear-right-add $a |- (
  ( ip u ( addV v w ) )
  =R
  ( addR ( ip u v ) ( ip u w ) )
) $.

ip-linear-right-smul $a |- (
  ( ip u ( smul a v ) ) =R ( mulR a ( ip u v ) )
) $.

ip-symm $a |- (
  ( ip u v ) =R ( ip v u )
) $.

$(
  The translated theorem family in the global structural context above.
$)
ip-neg-left $a |- (
  ( ip ( oppV u ) v ) =R ( oppR ( ip u v ) )
) $.

ip-neg-right $a |- (
  ( ip u ( oppV v ) ) =R ( oppR ( ip u v ) )
) $.

ip-add-add $a |- (
  ( ip ( addV u v ) ( addV u v ) )
  =R
  ( addR
    ( addR ( ip u u ) ( ip v u ) )
    ( addR ( ip u v ) ( ip v v ) )
  )
) $.

ip-sub-sub $a |- (
  ( ip ( subV u v ) ( subV u v ) )
  =R
  ( addR
    ( addR ( ip u u ) ( oppR ( ip v u ) ) )
    ( addR ( oppR ( ip u v ) ) ( ip v v ) )
  )
) $.

${
  pythagoras-orth-hyp $e |- (
    ( ip u v ) =R zeroR
  ) $.

  pythagoras $a |- (
    ( ip ( addV u v ) ( addV u v ) )
    =R
    ( addR ( ip u u ) ( ip v v ) )
  ) $.
$}

parallelogram $a |- (
  ( addR
    ( ip ( addV u v ) ( addV u v ) )
    ( ip ( subV u v ) ( subV u v ) )
  )
  =R
  ( addR
    ( addR
      ( addR ( ip u u ) ( ip v u ) )
      ( addR ( ip u v ) ( ip v v ) )
    )
    ( addR
      ( addR ( ip u u ) ( oppR ( ip v u ) ) )
      ( addR ( oppR ( ip u v ) ) ( ip v v ) )
    )
  )
) $.
