$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_left_goal1:
  under the generated integer-range, sortedness, bound, memory-validity,
  region, and linkedness assumptions, the original array prefix is strictly
  below the value selected at the computed midpoint. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses and size-type pairs are represented by ZZ X. ZZ, with their
  integer fields given by 1st and 2nd. NTP4VCShift is the generic cell-offset
  operation used by the imported predicates, while NTP4VCShiftSint32 is the
  source shift_sint32 operation and advances by the same logical index.
  NTP4VCValidRD, NTP4VCUint32, NTP4VCSint32, NTP4VCSorted,
  NTP4VCStrictUpperBound, NTP4VCStrictLowerBound, NTP4VCLowerBound, and
  NTP4VCUpperBound directly expand the corresponding source definitions.
  Every quantified array index ranges over all of ZZ. NTP4VCTDiv is
  truncating integer division toward zero; its only divisor in this statement
  is the positive integer two.

  The arbitrary integer-valued map R represents the source region function,
  membership of the allocation map T in the arbitrary set L represents
  linked, and the arbitrary map S represents to_uint32. The source range and
  in-range identity laws for to_uint32 are retained explicitly.

  NTP4VCX through NTP4VCX15 and NTP4VCA1 through NTP4VCA3 retain every source
  let-bound integer and address definition. Splitting the source curried
  implication chain into scoped essential hypotheses is bidirectionally
  equivalent for the arbitrary displayed parameters. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCSizeTypePair NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCShiftSint32
  NTP4VCUint32Limit NTP4VCSint32Limit NTP4VCTDiv
  NTP4VCX NTP4VCX1 NTP4VCX2 NTP4VCX3 NTP4VCX4 NTP4VCX5 NTP4VCX6
  NTP4VCX7 NTP4VCX8 NTP4VCX9 NTP4VCA1 NTP4VCX10 NTP4VCX11
  NTP4VCA2 NTP4VCX12 NTP4VCX13 NTP4VCX14 NTP4VCA3 NTP4VCX15
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32 NTP4VCIsSizeTypePair
  NTP4VCSorted NTP4VCStrictUpperBound NTP4VCStrictLowerBound
  NTP4VCLowerBound NTP4VCUpperBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-size-type-pair-class $a class NTP4VCSizeTypePair $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-shift-sint32-class $a class ( NTP4VCShiftSint32 A B ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B C ) $.
ntp4vc-x5-class $a class ( NTP4VCX5 A B C ) $.
ntp4vc-x6-class $a class ( NTP4VCX6 A B C ) $.
ntp4vc-x7-class $a class ( NTP4VCX7 A B C D ) $.
ntp4vc-x8-class $a class ( NTP4VCX8 A ) $.
ntp4vc-x9-class $a class ( NTP4VCX9 A B C ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A B C D ) $.
ntp4vc-x10-class $a class ( NTP4VCX10 A B C D E ) $.
ntp4vc-x11-class $a class ( NTP4VCX11 A B ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C ) $.
ntp4vc-x12-class $a class ( NTP4VCX12 A B C ) $.
ntp4vc-x13-class $a class ( NTP4VCX13 A B C ) $.
ntp4vc-x14-class $a class ( NTP4VCX14 A B C ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C D ) $.
ntp4vc-x15-class $a class ( NTP4VCX15 A B C ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-is-size-type-pair-syntax
  $a wff ( NTP4VCIsSizeTypePair A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
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
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-shift-sint32-def $a |- ( NTP4VCShiftSint32 A B ) =
  <.
    ( NTP4VCBase A ) ,
    ( ( NTP4VCOffset A ) + B )
  >. $.

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( 2nd ` A ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A ) = ( 1st ` A ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) = ( A + B ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A ) =
  ( -u ( NTP4VCX1 A ) ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A B C ) =
  ( ( B + C ) - ( NTP4VCX1 A ) ) $.
ntp4vc-x5-def $a |- ( NTP4VCX5 A B C ) =
  ( NTP4VCTDiv ( NTP4VCX4 A B C ) 2 ) $.
ntp4vc-x6-def $a |- ( NTP4VCX6 A B C ) =
  ( ( NTP4VCX1 A ) + ( NTP4VCX5 A B C ) ) $.
ntp4vc-x7-def $a |- ( NTP4VCX7 A B C D ) =
  (
    ( NTP4VCX1 A )
    +
    (
      D
      `
      (
        NTP4VCTDiv
          ( D ` ( NTP4VCX4 A B C ) )
          2
      )
    )
  ) $.
ntp4vc-x8-def $a |- ( NTP4VCX8 A ) = ( -u A ) $.
ntp4vc-x9-def $a |- ( NTP4VCX9 A B C ) =
  (
    (
      ( NTP4VCX1 A )
      +
      ( NTP4VCX5 A B C )
    )
    -
    B
  ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A B C D ) =
  ( NTP4VCShiftSint32 D ( NTP4VCX9 A B C ) ) $.
ntp4vc-x10-def $a |- ( NTP4VCX10 A B C D E ) =
  ( E ` ( NTP4VCA1 A B C D ) ) $.
ntp4vc-x11-def $a |- ( NTP4VCX11 A B ) =
  ( ( NTP4VCX1 A ) - B ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C ) =
  ( NTP4VCShiftSint32 C ( NTP4VCX11 A B ) ) $.
ntp4vc-x12-def $a |- ( NTP4VCX12 A B C ) =
  (
    (
      (
        1
        +
        ( NTP4VCX1 A )
      )
      +
      ( NTP4VCX5 A B C )
    )
    -
    B
  ) $.
ntp4vc-x13-def $a |- ( NTP4VCX13 A B C ) =
  ( -u ( NTP4VCX5 A B C ) ) $.
ntp4vc-x14-def $a |- ( NTP4VCX14 A B C ) =
  (
    (
      (
        (
          B
          +
          ( NTP4VCX A )
        )
        -
        1
      )
      -
      ( NTP4VCX1 A )
    )
    -
    ( NTP4VCX5 A B C )
  ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C D ) =
  ( NTP4VCShiftSint32 D ( NTP4VCX12 A B C ) ) $.
ntp4vc-x15-def $a |- ( NTP4VCX15 A B C ) =
  (
    (
      (
        (
          B
          +
          C
        )
        -
        1
      )
      -
      ( NTP4VCX1 A )
    )
    -
    ( NTP4VCX5 A B C )
  ) $.

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
    ( NTP4VCUint32 ( NTP4VCX1 A ) )
    /\
    ( NTP4VCUint32 ( NTP4VCX A ) )
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
        (
          C <_ x
          ->
          (
            x < y
            ->
            (
              ( A ` ( NTP4VCShift B x ) )
              <_
              ( A ` ( NTP4VCShift B y ) )
            )
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-strict-upper-bound-def $a |- (
    ( NTP4VCStrictUpperBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) < E
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-strict-lower-bound-def $a |- (
    ( NTP4VCStrictLowerBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          E < ( A ` ( NTP4VCShift B x ) )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-lower-bound-def $a |- (
    ( NTP4VCLowerBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          E <_ ( A ` ( NTP4VCShift B x ) )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-upper-bound-def $a |- (
    ( NTP4VCUpperBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) <_ E
        )
      )
  ) $.
$}

${
  $d x S $.

  $( Source parameters:
     A=s, B=i_1, C=i_3, D=a, E=t_1, F=i_2, G=i, and T=t.
     R is region, L is the extension of linked, and S is to_uint32. $)

  ntp4vc-size-pair $e |- A e. NTP4VCSizeTypePair $.
  ntp4vc-i1-integer $e |- B e. ZZ $.
  ntp4vc-i3-integer $e |- C e. ZZ $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-value-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-target-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- S e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( S ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( S ` x ) = x
    ) $.

  ntp4vc-i1-nonnegative $e |- 0 <_ B $.
  ntp4vc-i3-le-i2 $e |- C <_ F $.
  ntp4vc-x-le-i3 $e |- ( NTP4VCX A ) <_ C $.
  ntp4vc-x1-nonnegative $e |- 0 <_ ( NTP4VCX1 A ) $.
  ntp4vc-i1-le-x1 $e |- B <_ ( NTP4VCX1 A ) $.
  ntp4vc-x-nonnegative $e |- 0 <_ ( NTP4VCX A ) $.
  ntp4vc-x1-lt-x2 $e |- (
    ( NTP4VCX1 A ) < ( NTP4VCX2 B C )
  ) $.
  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-x5-nonnegative $e |- 0 <_ ( NTP4VCX5 A B C ) $.
  ntp4vc-i1-le-x5 $e |- B <_ ( NTP4VCX5 A B C ) $.
  ntp4vc-x6-lt-x2 $e |- (
    ( NTP4VCX6 A B C ) < ( NTP4VCX2 B C )
  ) $.
  ntp4vc-x6-lt-i1-plus-x $e |- (
    ( NTP4VCX6 A B C ) < ( B + ( NTP4VCX A ) )
  ) $.
  ntp4vc-i1-le-x7 $e |- B <_ ( NTP4VCX7 A B C S ) $.
  ntp4vc-x10-le-target $e |- (
    ( NTP4VCX10 A B C D E ) <_ G
  ) $.
  ntp4vc-target-le-x10 $e |- (
    G <_ ( NTP4VCX10 A B C D E )
  ) $.

  ntp4vc-x1-overflow-bound $e |- (
    ( NTP4VCX1 A ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-x-overflow-bound $e |- (
    ( NTP4VCX A ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-x2-overflow-bound $e |- (
    ( NTP4VCX2 B C ) <_
    (
      ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
      +
      ( NTP4VCX1 A )
    )
  ) $.
  ntp4vc-x5-overflow-bound $e |- (
    ( NTP4VCX5 A B C ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-x6-overflow-bound $e |- (
    ( NTP4VCX6 A B C ) <_
    (
      ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4
      +
      B
    )
  ) $.
  ntp4vc-x2-extended-overflow-bound $e |- (
    ( NTP4VCX2 B C ) <_
    (
      (
        ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6
        +
        ( NTP4VCX1 A )
      )
      +
      ( NTP4VCX5 A B C )
    )
  ) $.
  ntp4vc-x7-overflow-bound $e |- (
    ( NTP4VCX7 A B C S ) <_
    (
      ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
      +
      B
    )
  ) $.

  ntp4vc-is-size-pair $e |- ( NTP4VCIsSizeTypePair A ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-target-sint32 $e |- ( NTP4VCSint32 G ) $.
  ntp4vc-x1-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX1 A ) ) $.
  ntp4vc-x-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX A ) ) $.

  ntp4vc-array-sorted $e |- (
    NTP4VCSorted E D 0 F
  ) $.
  ntp4vc-x11-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX11 A B )
  ) $.
  ntp4vc-suffix-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound E D C F G
  ) $.
  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShiftSint32 D 0 ) F
  ) $.
  ntp4vc-prefix-strict-upper-bound $e |- (
    NTP4VCStrictUpperBound E D 0 ( NTP4VCX11 A B ) G
  ) $.
  ntp4vc-left-valid-rd $e |- (
    NTP4VCValidRD
      T
      ( NTP4VCA2 A B D )
      ( NTP4VCX5 A B C )
  ) $.
  ntp4vc-left-sorted $e |- (
    NTP4VCSorted
      E
      ( NTP4VCA2 A B D )
      0
      ( NTP4VCX5 A B C )
  ) $.
  ntp4vc-x9-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX9 A B C )
  ) $.
  ntp4vc-x12-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX12 A B C )
  ) $.
  ntp4vc-x14-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX14 A B C )
  ) $.
  ntp4vc-x10-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX10 A B C D E )
  ) $.
  ntp4vc-midpoint-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCA1 A B C D ) 1
  ) $.
  ntp4vc-right-valid-rd $e |- (
    NTP4VCValidRD
      T
      ( NTP4VCA3 A B C D )
      ( NTP4VCX15 A B C )
  ) $.
  ntp4vc-right-sorted $e |- (
    NTP4VCSorted
      E
      ( NTP4VCA3 A B C D )
      0
      ( NTP4VCX15 A B C )
  ) $.
  ntp4vc-left-strict-upper-bound-x10 $e |- (
    NTP4VCStrictUpperBound
      E
      ( NTP4VCA2 A B D )
      0
      B
      ( NTP4VCX10 A B C D E )
  ) $.
  ntp4vc-right-strict-lower-bound-x10 $e |- (
    NTP4VCStrictLowerBound
      E
      ( NTP4VCA3 A B C D )
      ( NTP4VCX14 A B C )
      ( NTP4VCX15 A B C )
      ( NTP4VCX10 A B C D E )
  ) $.
  ntp4vc-left-lower-bound-x10 $e |- (
    NTP4VCLowerBound
      E
      ( NTP4VCA2 A B D )
      B
      ( NTP4VCX5 A B C )
      ( NTP4VCX10 A B C D E )
  ) $.
  ntp4vc-right-upper-bound-x10 $e |- (
    NTP4VCUpperBound
      E
      ( NTP4VCA3 A B C D )
      0
      ( NTP4VCX14 A B C )
      ( NTP4VCX10 A B C D E )
  ) $.

  ntp4vc-equal-range-post-left-goal1 $a |- (
    NTP4VCStrictUpperBound
      E
      D
      0
      ( NTP4VCX1 A )
      ( NTP4VCX10 A B C D E )
  ) $.
$}
