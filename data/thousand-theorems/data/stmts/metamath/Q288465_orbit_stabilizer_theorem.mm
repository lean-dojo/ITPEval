$(
  Statement-only formalization of Thousand Theorems corpus artifact Q288465
  (thousand-theorems__metamath__Q288465), "Orbit-stabilizer theorem": for an
  arbitrary group action and point, the point's orbit is in bijection with
  the left-coset quotient of the group by the point stabilizer. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q288465Stabilizer G Y A b is the subgroup carrier of elements of G fixing
  b under the action A. Q288465OrbitRel G Y A is the orbit equivalence
  relation on Y. Q288465OrbitMap G Y A b sends the left coset of g modulo
  the stabilizer to A(g,b).

  The final $a assertion says that this canonical map is a bijection from the
  left-coset quotient onto the orbit of b. Its inverse is the equivalence from
  the orbit to the quotient represented by
  MulAction.orbitEquivQuotientStabilizer. The auxiliary $a declarations are
  syntax or faithful definitions; this file contains no $p proof statement.
$)

$c Q288465Stabilizer Q288465OrbitRel Q288465OrbitMap $.

q288465-stabilizer-syntax $a class
  ( Q288465Stabilizer G Y A b ) $.
q288465-orbit-rel-syntax $a class
  ( Q288465OrbitRel G Y A ) $.
q288465-orbit-map-syntax $a class
  ( Q288465OrbitMap G Y A b ) $.

${
  $d A G Y b u $.

  q288465-stabilizer-definition $a |-
    ( Q288465Stabilizer G Y A b )
    =
    { u e. ( Base ` G ) | ( A ` <. u , b >. ) = b }
  $.
$}

${
  $d A G Y g x y $.

  q288465-orbit-rel-definition $a |-
    ( Q288465OrbitRel G Y A )
    =
    { <. x , y >. |
      (
        { x , y } C_ Y
        /\
        E. g e. ( Base ` G ) ( A ` <. g , x >. ) = y
      )
    }
  $.
$}

${
  $d A G Y b g $.

  q288465-orbit-map-definition $a |-
    ( Q288465OrbitMap G Y A b )
    =
    ran
    (
      g e. ( Base ` G )
      |->
      <.
        [ g ] ( G ~QG ( Q288465Stabilizer G Y A b ) )
        ,
        ( A ` <. g , b >. )
      >.
    )
  $.
$}

${
  $d A G Y b $.

  thousand-theorems-q288465-orbit-stabilizer-theorem $a |- (
    A. G A. Y A. A A. b
      (
        (
          A e. ( G GrpAct Y )
          /\
          b e. Y
        )
        ->
        ( Q288465OrbitMap G Y A b )
        :
        (
          ( Base ` G )
          /.
          ( G ~QG ( Q288465Stabilizer G Y A b ) )
        )
        -1-1-onto->
        [ b ] ( Q288465OrbitRel G Y A )
      )
  ) $.
$}
