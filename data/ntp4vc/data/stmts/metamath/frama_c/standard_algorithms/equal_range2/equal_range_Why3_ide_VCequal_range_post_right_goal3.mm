$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_right_goal3:
  the equal-range post-right verification condition concludes that every
  array element from the returned second index to the original upper bound
  is strictly greater than the searched value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses and size-type pairs are represented by ZZ X. ZZ. The generic
  shift inside the imported range predicates advances an address offset by
  its integer argument; NTP4VCShiftSint32 is the source shift_sint32 operation
  from this artifact's pinned Compound theory and is definitionally the same
  unscaled shift. Integer arithmetic, order, equality, total functions, and
  quantification are SetMM's standard objects. NTP4VCTDiv at divisor two is
  integer division truncated toward zero, as required by the pinned Why3
  source.

  R represents region, membership of the allocation map F in the arbitrary
  set L represents linked, and S represents to_uint32 with its source range
  and in-range identity laws. The guarded branch hypotheses are logically
  equivalent to the source if-then-else conjunction. The final $a declaration
  is Metamath's native unproved statement encoding; there is no $p proof.
$)

$c
  NTP4VCAddr NTP4VCSizeTypePair NTP4VCBool
  NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCShiftSint32
  NTP4VCUint32Limit NTP4VCUint32Max NTP4VCUint32MaxMinusOne
  NTP4VCSint32Limit NTP4VCTDiv
  NTP4VCX NTP4VCX2 NTP4VCX3 NTP4VCX4 NTP4VCX5
  NTP4VCA1 NTP4VCX6 NTP4VCX7 NTP4VCA2 NTP4VCA3
  NTP4VCX9 NTP4VCX10 NTP4VCX11
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32 NTP4VCIsSizeTypePair
  NTP4VCSorted NTP4VCStrictUpperBound NTP4VCStrictLowerBound
  NTP4VCLowerBound NTP4VCUpperBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-size-type-pair-class $a class NTP4VCSizeTypePair $.
ntp4vc-bool-class $a class NTP4VCBool $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint32-max-class $a class NTP4VCUint32Max $.
ntp4vc-uint32-max-minus-one-class $a class NTP4VCUint32MaxMinusOne $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-shift-sint32-class $a class ( NTP4VCShiftSint32 A B ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B ) $.
ntp4vc-x5-class $a class ( NTP4VCX5 A ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A B C ) $.
ntp4vc-x6-class $a class ( NTP4VCX6 A B C D ) $.
ntp4vc-x7-class $a class ( NTP4VCX7 A B C ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C ) $.
ntp4vc-x9-class $a class ( NTP4VCX9 A B ) $.
ntp4vc-x10-class $a class ( NTP4VCX10 A B ) $.
ntp4vc-x11-class $a class ( NTP4VCX11 A B C ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-is-size-type-pair-syntax $a wff ( NTP4VCIsSizeTypePair A ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-strict-upper-bound-syntax
  $a wff ( NTP4VCStrictUpperBound A B C D E ) $.
ntp4vc-strict-lower-bound-syntax
  $a wff ( NTP4VCStrictLowerBound A B C D E ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-size-type-pair-def
  $a |- NTP4VCSizeTypePair = ( ZZ X. ZZ ) $.
ntp4vc-bool-def $a |- NTP4VCBool = { 0 , 1 } $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint32-max-def $a |- NTP4VCUint32Max =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 $.
ntp4vc-uint32-max-minus-one-def $a |- NTP4VCUint32MaxMinusOne =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-shift-sint32-def $a |- ( NTP4VCShiftSint32 A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if ( A < 0 , ( |^ ` ( A / B ) ) , ( |_ ` ( A / B ) ) ) $.

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( 1st ` A ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) = ( A - B ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) =
  ( NTP4VCTDiv ( NTP4VCX2 A B ) 2 ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A B ) =
  ( B + ( NTP4VCX3 A B ) ) $.
ntp4vc-x5-def $a |- ( NTP4VCX5 A ) = ( 2nd ` A ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A B C ) =
  ( NTP4VCShiftSint32 A ( NTP4VCX4 B C ) ) $.
ntp4vc-x6-def $a |- ( NTP4VCX6 A B C D ) =
  ( A ` ( NTP4VCA1 B C D ) ) $.
ntp4vc-x7-def $a |- ( NTP4VCX7 A B C ) =
  (
    C
    +
    (
      A
      `
      ( NTP4VCTDiv ( A ` ( NTP4VCX2 B C ) ) 2 )
    )
  ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) =
  ( NTP4VCShiftSint32 A B ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C ) =
  ( NTP4VCShiftSint32 A ( ( 1 + C ) + ( NTP4VCX3 B C ) ) ) $.
ntp4vc-x9-def $a |- ( NTP4VCX9 A B ) =
  ( ( ( A - 1 ) - B ) - ( NTP4VCX3 A B ) ) $.
ntp4vc-x10-def $a |- ( NTP4VCX10 A B ) =
  ( ( NTP4VCX A ) - B ) $.
ntp4vc-x11-def $a |- ( NTP4VCX11 A B C ) =
  ( ( ( ( NTP4VCX5 A ) - 1 ) - C ) - ( NTP4VCX3 B C ) ) $.

ntp4vc-valid-rd-def $a |- ( ( NTP4VCValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NTP4VCBase B ) =/= 0
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
) $.
ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.
ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.
ntp4vc-is-size-type-pair-def $a |- (
  ( NTP4VCIsSizeTypePair A )
  <->
  (
    ( NTP4VCUint32 ( NTP4VCX A ) )
    /\
    ( NTP4VCUint32 ( NTP4VCX5 A ) )
  )
) $.

${
  $d x y $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  ntp4vc-sorted-def $a |- (
    ( NTP4VCSorted A B C D )
    <->
    A. x e. ZZ A. y e. ZZ
      (
        y < D
        ->
        ( C <_ x -> ( x < y ->
          ( A ` ( NTP4VCShift B x ) ) <_
          ( A ` ( NTP4VCShift B y ) ) ) )
      )
  ) $.
$}
${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  ntp4vc-strict-upper-bound-def $a |- (
    ( NTP4VCStrictUpperBound A B C D E )
    <->
    A. x e. ZZ
      ( C <_ x -> ( x < D -> ( A ` ( NTP4VCShift B x ) ) < E ) )
  ) $.
  ntp4vc-strict-lower-bound-def $a |- (
    ( NTP4VCStrictLowerBound A B C D E )
    <->
    A. x e. ZZ
      ( C <_ x -> ( x < D -> E < ( A ` ( NTP4VCShift B x ) ) ) )
  ) $.
  ntp4vc-lower-bound-def $a |- (
    ( NTP4VCLowerBound A B C D E )
    <->
    A. x e. ZZ
      ( C <_ x -> ( x < D -> E <_ ( A ` ( NTP4VCShift B x ) ) ) )
  ) $.
  ntp4vc-upper-bound-def $a |- (
    ( NTP4VCUpperBound A B C D E )
    <->
    A. x e. ZZ
      ( C <_ x -> ( x < D -> ( A ` ( NTP4VCShift B x ) ) <_ E ) )
  ) $.
$}

${
  $d x S $.

  $( A=s, B=i_8, C=i_10, D=a, E=t_1, F=t, G=i_11, H=i_7,
     I=i_1, J=i_2, K=i_3, M=i_4, N=i_5, O=i_6, P=i_9,
     Q=i, U=p_1, V=p_2, W=p_3, Y=p. $)

  ntp4vc-size-pair $e |- A e. NTP4VCSizeTypePair $.
  ntp4vc-i8-integer $e |- B e. ZZ $.
  ntp4vc-i10-integer $e |- C e. ZZ $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-value-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-i11-integer $e |- G e. ZZ $.
  ntp4vc-i7-integer $e |- H e. ZZ $.
  ntp4vc-i1-integer $e |- I e. ZZ $.
  ntp4vc-i2-integer $e |- J e. ZZ $.
  ntp4vc-i3-integer $e |- K e. ZZ $.
  ntp4vc-i4-integer $e |- M e. ZZ $.
  ntp4vc-i5-integer $e |- N e. ZZ $.
  ntp4vc-i6-integer $e |- O e. ZZ $.
  ntp4vc-i9-integer $e |- P e. ZZ $.
  ntp4vc-target-integer $e |- Q e. ZZ $.
  ntp4vc-p1-bool $e |- U e. NTP4VCBool $.
  ntp4vc-p2-bool $e |- V e. NTP4VCBool $.
  ntp4vc-p3-bool $e |- W e. NTP4VCBool $.
  ntp4vc-p-bool $e |- Y e. NTP4VCBool $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- S e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( S ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( S ` x ) = x ) $.

  ntp4vc-i8-le-i7 $e |- B <_ H $.
  ntp4vc-i11-le-i8 $e |- G <_ B $.
  ntp4vc-i11-nonnegative $e |- 0 <_ G $.
  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-is-size-pair $e |- ( NTP4VCIsSizeTypePair A ) $.
  ntp4vc-linked-allocation $e |- F e. L $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 I ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 K ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 M ) $.
  ntp4vc-i5-uint32 $e |- ( NTP4VCUint32 N ) $.
  ntp4vc-i6-uint32 $e |- ( NTP4VCUint32 O ) $.
  ntp4vc-i7-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-i8-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i9-uint32 $e |- ( NTP4VCUint32 P ) $.
  ntp4vc-i10-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i11-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-target-sint32 $e |- ( NTP4VCSint32 Q ) $.
  ntp4vc-array-sorted $e |- ( NTP4VCSorted E D 0 H ) $.
  ntp4vc-prefix-strict-upper-bound $e |- (
    NTP4VCStrictUpperBound E D 0 G Q
  ) $.
  ntp4vc-suffix-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound E D B H Q
  ) $.
  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCShiftSint32 D 0 ) H
  ) $.

  ntp4vc-then-p1 $e |- ( G < B -> U = 0 ) $.
  ntp4vc-then-p2 $e |- ( G < B -> V = 0 ) $.
  ntp4vc-then-p3 $e |- ( G < B -> W = 0 ) $.
  ntp4vc-then-i2-i1 $e |- ( G < B -> J = I ) $.
  ntp4vc-then-i5-i4 $e |- ( G < B -> N = M ) $.
  ntp4vc-then-i10-i9 $e |- ( G < B -> C = P ) $.
  ntp4vc-then-i11-i10 $e |- ( G < B -> G = C ) $.
  ntp4vc-then-x-i3-i10 $e |- (
    G < B -> ( NTP4VCX A ) = ( K + C )
  ) $.
  ntp4vc-then-x-i6-i10 $e |- (
    G < B -> ( NTP4VCX A ) = ( O + C )
  ) $.
  ntp4vc-then-x4-i4 $e |- ( G < B -> ( NTP4VCX4 B C ) = M ) $.
  ntp4vc-then-x4-i5 $e |- ( G < B -> ( NTP4VCX4 B C ) = N ) $.
  ntp4vc-then-x5-i1 $e |- (
    G < B ->
    ( NTP4VCX5 A ) = ( ( ( 1 + I ) + C ) + ( NTP4VCX3 B C ) )
  ) $.
  ntp4vc-then-x5-i2 $e |- (
    G < B ->
    ( NTP4VCX5 A ) = ( ( ( 1 + J ) + C ) + ( NTP4VCX3 B C ) )
  ) $.
  ntp4vc-then-x5-le-i8 $e |- ( G < B -> ( NTP4VCX5 A ) <_ B ) $.
  ntp4vc-then-x-nonnegative $e |- ( G < B -> 0 <_ ( NTP4VCX A ) ) $.
  ntp4vc-then-i10-le-x $e |- ( G < B -> C <_ ( NTP4VCX A ) ) $.
  ntp4vc-then-x5-nonnegative $e |- (
    G < B -> 0 <_ ( NTP4VCX5 A )
  ) $.
  ntp4vc-then-x3-nonnegative $e |- (
    G < B -> 0 <_ ( NTP4VCX3 B C )
  ) $.
  ntp4vc-then-x4-lt-i8 $e |- ( G < B -> ( NTP4VCX4 B C ) < B ) $.
  ntp4vc-then-x-le-x4 $e |- (
    G < B -> ( NTP4VCX A ) <_ ( NTP4VCX4 B C )
  ) $.
  ntp4vc-then-x4-lt-x5 $e |- (
    G < B -> ( NTP4VCX4 B C ) < ( NTP4VCX5 A )
  ) $.
  ntp4vc-then-x6-le-i $e |- (
    G < B -> ( NTP4VCX6 E D B C ) <_ Q
  ) $.
  ntp4vc-then-x7-nonnegative $e |- (
    G < B -> 0 <_ ( NTP4VCX7 S B C )
  ) $.
  ntp4vc-then-i-le-x6 $e |- (
    G < B -> Q <_ ( NTP4VCX6 E D B C )
  ) $.
  ntp4vc-then-x-max $e |- (
    G < B -> ( NTP4VCX A ) <_ NTP4VCUint32Max
  ) $.
  ntp4vc-then-x5-max $e |- (
    G < B -> ( NTP4VCX5 A ) <_ NTP4VCUint32Max
  ) $.
  ntp4vc-then-i8-bound $e |- (
    G < B -> B <_ ( NTP4VCUint32Max + C )
  ) $.
  ntp4vc-then-x3-max $e |- (
    G < B -> ( NTP4VCX3 B C ) <_ NTP4VCUint32Max
  ) $.
  ntp4vc-then-x4-max $e |- (
    G < B -> ( NTP4VCX4 B C ) <_ NTP4VCUint32MaxMinusOne
  ) $.
  ntp4vc-then-i8-extended-bound $e |- (
    G < B ->
    B <_ ( ( NTP4VCUint32Limit + C ) + ( NTP4VCX3 B C ) )
  ) $.
  ntp4vc-then-x7-max $e |- (
    G < B -> ( NTP4VCX7 S B C ) <_ NTP4VCUint32Max
  ) $.
  ntp4vc-then-left-valid $e |- (
    G < B ->
    ( NTP4VCValidRD F ( NTP4VCA2 D C ) ( NTP4VCX3 B C ) )
  ) $.
  ntp4vc-then-left-sorted $e |- (
    G < B ->
    ( NTP4VCSorted E ( NTP4VCA2 D C ) 0 ( NTP4VCX3 B C ) )
  ) $.
  ntp4vc-then-middle-valid $e |- (
    G < B -> ( NTP4VCValidRD F ( NTP4VCA1 D B C ) 1 )
  ) $.
  ntp4vc-then-right-valid $e |- (
    G < B ->
    ( NTP4VCValidRD F ( NTP4VCA3 D B C ) ( NTP4VCX9 B C ) )
  ) $.
  ntp4vc-then-right-sorted $e |- (
    G < B ->
    ( NTP4VCSorted E ( NTP4VCA3 D B C ) 0 ( NTP4VCX9 B C ) )
  ) $.
  ntp4vc-then-strict-upper $e |- (
    G < B ->
    (
      NTP4VCStrictUpperBound
        E ( NTP4VCA2 D C ) 0 ( NTP4VCX10 A C )
        ( NTP4VCX6 E D B C )
    )
  ) $.
  ntp4vc-then-strict-lower $e |- (
    G < B ->
    (
      NTP4VCStrictLowerBound
        E ( NTP4VCA3 D B C ) ( NTP4VCX11 A B C )
        ( NTP4VCX9 B C ) ( NTP4VCX6 E D B C )
    )
  ) $.
  ntp4vc-then-lower $e |- (
    G < B ->
    (
      NTP4VCLowerBound
        E ( NTP4VCA2 D C ) ( NTP4VCX10 A C )
        ( NTP4VCX3 B C ) ( NTP4VCX6 E D B C )
    )
  ) $.
  ntp4vc-then-upper $e |- (
    G < B ->
    (
      NTP4VCUpperBound
        E ( NTP4VCA3 D B C ) 0 ( NTP4VCX11 A B C )
        ( NTP4VCX6 E D B C )
    )
  ) $.

  ntp4vc-else-p $e |- ( -. ( G < B ) -> Y = 0 ) $.
  ntp4vc-else-x-i11 $e |- (
    -. ( G < B ) -> ( NTP4VCX A ) = G
  ) $.
  ntp4vc-else-x5-x $e |- (
    -. ( G < B ) -> ( NTP4VCX5 A ) = ( NTP4VCX A )
  ) $.

  ntp4vc-equal-range-post-right-goal3 $a |- (
    NTP4VCStrictLowerBound E D ( NTP4VCX5 A ) H Q
  ) $.
$}
