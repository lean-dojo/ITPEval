$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b3: the largest radius of a circle contained in the
  four-dimensional hypercube of side length one is sqrt(2) / 2. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The four-element interval 0 ..^ 4 is the source carrier Fin 4, so P08B3R4 is the
  full real Euclidean four-space. P08B3Cube is the coordinate hypercube
  [-1/2,1/2]^4. P08B3Combo(s,P,t,Q) is the vector sP+tQ,
  P08B3Affine(C,s,P,t,Q) is C+sP+tQ, and P08B3Norm is the ordinary
  Euclidean norm.

  P08B3Independent(P,Q) states genuine real linear independence. Thus the
  internally existential C, P, and Q in P08B3Contains(r) determine an
  arbitrary two-dimensional affine plane, and its universal clause says
  that every point in that plane at distance r from C belongs to the
  hypercube. This is exactly the source sphere-intersection containment
  predicate, with the plane represented by a basis.

  The final conjunction expands IsGreatest: sqrt(2)/2 is an attained
  contained-circle radius, and every contained-circle radius is at most
  sqrt(2)/2. All auxiliary $a declarations are syntax or explicit
  definitions; this database contains no $p proof declaration.
$)

$c P08B3R4 P08B3Cube P08B3Combo P08B3Affine P08B3Norm
   P08B3Independent P08B3Contains P08B3Solution $.

p08b3-space-syntax $a class P08B3R4 $.
p08b3-cube-syntax $a class P08B3Cube $.
p08b3-combo-syntax $a class ( P08B3Combo s P t Q ) $.
p08b3-affine-syntax $a class ( P08B3Affine C s P t Q ) $.
p08b3-norm-syntax $a class ( P08B3Norm V ) $.
p08b3-independent-syntax $a wff ( P08B3Independent P Q ) $.
p08b3-contains-syntax $a wff ( P08B3Contains r ) $.
p08b3-solution-syntax $a class P08B3Solution $.

p08b3-space-definition $a |- P08B3R4 = ( RR ^m ( 0 ..^ 4 ) ) $.

${
  $d i x $.

  p08b3-cube-definition $a |- P08B3Cube = {
    x e. P08B3R4 |
      A. i e. ( 0 ..^ 4 )
        ( abs ` ( x ` i ) ) <_ ( 1 / 2 )
  } $.
$}

${
  $d P Q i s t $.

  p08b3-combo-definition $a |- (
    P08B3Combo s P t Q
  ) = (
    i e. ( 0 ..^ 4 ) |->
      (
        ( s x. ( P ` i ) )
        +
        ( t x. ( Q ` i ) )
      )
  ) $.
$}

${
  $d C P Q i s t $.

  p08b3-affine-definition $a |- (
    P08B3Affine C s P t Q
  ) = (
    i e. ( 0 ..^ 4 ) |->
      (
        ( C ` i )
        +
        (
          ( s x. ( P ` i ) )
          +
          ( t x. ( Q ` i ) )
        )
      )
  ) $.
$}

${
  $d V i $.

  p08b3-norm-definition $a |- (
    P08B3Norm V
  ) = (
    sqrt
    `
    (
      sum_ i e. ( 0 ..^ 4 )
        ( ( V ` i ) ^ 2 )
    )
  ) $.
$}

${
  $d P Q a b i $.

  p08b3-independent-definition $a |- (
    ( P08B3Independent P Q )
    <->
    A. a e. RR A. b e. RR
      (
        (
          A. i e. ( 0 ..^ 4 )
            (
              (
                ( a x. ( P ` i ) )
                +
                ( b x. ( Q ` i ) )
              )
              =
              0
            )
        )
        ->
        ( a = 0 /\ b = 0 )
      )
  ) $.
$}

${
  $d c p q r s t $.

  p08b3-contains-definition $a |- (
    ( P08B3Contains r )
    <->
    E. c e. P08B3R4 E. p e. P08B3R4 E. q e. P08B3R4
      (
        ( P08B3Independent p q )
        /\
        A. s e. RR A. t e. RR
          (
            ( P08B3Norm ( P08B3Combo s p t q ) ) = r
            ->
            ( P08B3Affine c s p t q ) e. P08B3Cube
          )
      )
  ) $.
$}

p08b3-solution-definition $a |-
  P08B3Solution = ( ( sqrt ` 2 ) / 2 ) $.

putnambench-putnam-2008-b3 $a |- (
  ( P08B3Contains P08B3Solution )
  /\
  A. r e. RR
    (
      ( P08B3Contains r )
      ->
      r <_ P08B3Solution
    )
) $.
