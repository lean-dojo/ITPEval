$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_upper_bound_pre_sorted_goal28:
  under the generated integer-range, sortedness, bound, memory-validity,
  region, and linkedness assumptions, the suffix passed to upper_bound is
  sorted. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift is the source generic shift operation and
  advances the logical offset by its integer argument; NTP4VCShiftSint32 is
  the source shift_sint32 operation and advances it by the same index.
  NTP4VCValidRD, NTP4VCUint32,
  NTP4VCSint32, NTP4VCSorted, NTP4VCStrictUpperBound,
  NTP4VCStrictLowerBound, and NTP4VCLowerBound directly expand the
  corresponding source definitions. Every quantified array index ranges over
  all of ZZ. NTP4VCTDiv is truncating integer division toward zero; its only
  divisor in this statement is the positive integer two.

  The arbitrary integer-valued map R represents the source region function,
  membership of the allocation map T in the arbitrary set L represents
  linked, and the arbitrary map S represents to_uint32. The source range and
  in-range identity laws for to_uint32 are retained explicitly.

  NTP4VCX through NTP4VCX7 and NTP4VCA1 through NTP4VCA2 retain every source
  let-bound integer and address definition. Splitting the source curried
  implication chain into scoped essential hypotheses is bidirectionally
  equivalent for the arbitrary displayed parameters. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCShiftSint32
  NTP4VCUint32Limit NTP4VCSint32Limit NTP4VCTDiv
  NTP4VCX NTP4VCX1 NTP4VCX2 NTP4VCX3 NTP4VCX4
  NTP4VCA1 NTP4VCX5 NTP4VCX6 NTP4VCA2 NTP4VCX7
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32
  NTP4VCSorted NTP4VCStrictUpperBound NTP4VCStrictLowerBound
  NTP4VCLowerBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-shift-sint32-class $a class ( NTP4VCShiftSint32 A B ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A B C ) $.
ntp4vc-x5-class $a class ( NTP4VCX5 A B C D ) $.
ntp4vc-x6-class $a class ( NTP4VCX6 A B C ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-x7-class $a class ( NTP4VCX7 A B ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-strict-upper-bound-syntax
  $a wff ( NTP4VCStrictUpperBound A B C D E ) $.
ntp4vc-strict-lower-bound-syntax
  $a wff ( NTP4VCStrictLowerBound A B C D E ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <.
    ( NTP4VCBase A )
    ,
    ( ( NTP4VCOffset A ) + B )
  >. $.
ntp4vc-shift-sint32-def $a |- ( NTP4VCShiftSint32 A B ) =
  <.
    ( NTP4VCBase A )
    ,
    ( ( NTP4VCOffset A ) + B )
  >. $.

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A + B ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A ) = ( -u A ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) = ( A - B ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) =
  ( NTP4VCTDiv ( NTP4VCX2 A B ) 2 ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A B ) =
  ( B + ( NTP4VCX3 A B ) ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A B C ) =
  ( NTP4VCShiftSint32 A ( NTP4VCX4 B C ) ) $.
ntp4vc-x5-def $a |- ( NTP4VCX5 A B C D ) =
  ( A ` ( NTP4VCA1 B C D ) ) $.
ntp4vc-x6-def $a |- ( NTP4VCX6 A B C ) =
  (
    B
    +
    (
      A
      `
      ( NTP4VCTDiv ( A ` ( NTP4VCX2 C B ) ) 2 )
    )
  ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) =
  ( NTP4VCShiftSint32 A B ) $.
ntp4vc-x7-def $a |- ( NTP4VCX7 A B ) =
  ( ( 1 + B ) + ( NTP4VCX3 A B ) ) $.

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
  $d x S $.

  $( Source parameters:
     A=i_1, B=i_4, C=i_3, D=a, E=t_1, F=i_2, G=i, and T=t.
     R is region, L is the extension of linked, and S is to_uint32. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i4-integer $e |- B e. ZZ $.
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

  ntp4vc-i1-nonnegative $e |- 0 <_ A $.
  ntp4vc-i3-le-i2 $e |- C <_ F $.
  ntp4vc-i4-le-i3 $e |- B <_ C $.
  ntp4vc-i4-nonnegative $e |- 0 <_ B $.
  ntp4vc-i4-lt-i3 $e |- B < C $.
  ntp4vc-x-nonnegative $e |- 0 <_ ( NTP4VCX A B ) $.
  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-x3-nonnegative $e |- 0 <_ ( NTP4VCX3 C B ) $.
  ntp4vc-i1-le-x3 $e |- A <_ ( NTP4VCX3 C B ) $.
  ntp4vc-x4-lt-i3 $e |- ( NTP4VCX4 C B ) < C $.
  ntp4vc-x5-le-target $e |- ( NTP4VCX5 E D C B ) <_ G $.
  ntp4vc-x6-nonnegative $e |- 0 <_ ( NTP4VCX6 S B C ) $.
  ntp4vc-target-le-x5 $e |- G <_ ( NTP4VCX5 E D C B ) $.

  ntp4vc-x-overflow-bound $e |- (
    ( NTP4VCX A B ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-i3-overflow-bound $e |- (
    C <_ (
      ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 + B
    )
  ) $.
  ntp4vc-x3-overflow-bound $e |- (
    ( NTP4VCX3 C B ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-x4-overflow-bound $e |- (
    ( NTP4VCX4 C B ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4
  ) $.
  ntp4vc-i3-extended-overflow-bound $e |- (
    C <_ (
      (
        ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6
        + B
      )
      +
      ( NTP4VCX3 C B )
    )
  ) $.
  ntp4vc-x6-overflow-bound $e |- (
    ( NTP4VCX6 S B C ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.

  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-target-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-array-sorted $e |- (
    NTP4VCSorted E D 0 F
  ) $.
  ntp4vc-prefix-strict-upper-bound $e |- (
    NTP4VCStrictUpperBound E D 0 B G
  ) $.
  ntp4vc-suffix-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound E D C F G
  ) $.
  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShiftSint32 D 0 ) F
  ) $.
  ntp4vc-prefix-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCA2 D B ) ( NTP4VCX3 C B )
  ) $.
  ntp4vc-prefix-sorted $e |- (
    NTP4VCSorted E ( NTP4VCA2 D B ) 0 ( NTP4VCX3 C B )
  ) $.
  ntp4vc-x4-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX4 C B )
  ) $.
  ntp4vc-x7-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX7 C B )
  ) $.
  ntp4vc-x5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX5 E D C B )
  ) $.
  ntp4vc-midpoint-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCA1 D C B ) 1
  ) $.
  ntp4vc-prefix-strict-upper-bound-x5 $e |- (
    NTP4VCStrictUpperBound
      E ( NTP4VCA2 D B ) 0 A ( NTP4VCX5 E D C B )
  ) $.
  ntp4vc-prefix-lower-bound-x5 $e |- (
    NTP4VCLowerBound
      E
      ( NTP4VCA2 D B )
      A
      ( NTP4VCX3 C B )
      ( NTP4VCX5 E D C B )
  ) $.

  ntp4vc-equal-range-call-upper-bound-pre-sorted-goal28 $a |- (
    NTP4VCSorted
      E
      ( NTP4VCShiftSint32 D ( NTP4VCX7 C B ) )
      0
      (
        (
          ( C - 1 ) - B
        )
        -
        ( NTP4VCX3 C B )
      )
  ) $.
$}
