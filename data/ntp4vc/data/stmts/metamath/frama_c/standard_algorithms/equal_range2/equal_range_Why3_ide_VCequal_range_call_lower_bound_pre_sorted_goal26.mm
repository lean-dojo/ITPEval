$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26:
  under the generated integer-range, sortedness, strict-bound,
  memory-validity, region, and linkedness assumptions, the prefix passed to
  lower_bound is sorted. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift is the imported generic address shift by an
  integer offset, while NTP4VCShiftSint32 is the source shift_sint32
  operation and therefore advances by one logical memory cell. NTP4VCValidRD,
  NTP4VCUint32, NTP4VCSint32, NTP4VCSorted,
  NTP4VCStrictUpperBound, and NTP4VCStrictLowerBound directly expand the
  corresponding source definitions. Every quantified array index ranges
  over all of ZZ.
  NTP4VCTDiv is truncating integer division toward zero; its only divisor in
  this statement is the positive integer two.

  The arbitrary integer-valued map R represents the source region function,
  and membership of the allocation map T in the arbitrary set L represents
  linked. No additional laws are assigned to either imported symbol.

  Source x is B-C and source x_1 is NTP4VCX1(B,C). The remaining let-bound
  terms x_2, a_1, and x_3 are retained by NTP4VCX2, NTP4VCA1, and
  NTP4VCX3. Source x_4 reduces to C+NTP4VCX1(B,C): the retained inequalities
  C <= B and B <= 4294967295+C make x uint32, while the retained bounds on
  x_1 make x_1 uint32, so both source to_uint32 applications are identities.
  NTP4VCX4 records this equivalent value explicitly.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCShiftSint32
  NTP4VCUint32Limit NTP4VCSint32Limit NTP4VCTDiv
  NTP4VCX1 NTP4VCX2 NTP4VCA1 NTP4VCX3 NTP4VCX4
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32
  NTP4VCSorted NTP4VCStrictUpperBound NTP4VCStrictLowerBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-shift-sint32-class $a class ( NTP4VCShiftSint32 A B ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A B C ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B C D ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B ) $.

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

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-shift-sint32-def $a |- ( NTP4VCShiftSint32 A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) =
  ( NTP4VCTDiv ( A - B ) 2 ) $.

ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) =
  ( B + ( NTP4VCX1 A B ) ) $.

ntp4vc-a1-def $a |- ( NTP4VCA1 A B C ) =
  ( NTP4VCShiftSint32 A ( NTP4VCX2 B C ) ) $.

ntp4vc-x3-def $a |- ( NTP4VCX3 A B C D ) =
  ( A ` ( NTP4VCA1 B C D ) ) $.

ntp4vc-x4-def $a |- ( NTP4VCX4 A B ) =
  ( B + ( NTP4VCX1 A B ) ) $.

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
  $( Source parameters:
     A=a, B=i_2, C=i_3, D=t_1, E=i_1, F=i, and T=t.
     R is region and L is the extension of linked. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- B e. ZZ $.
  ntp4vc-i3-integer $e |- C e. ZZ $.
  ntp4vc-value-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-target-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i2-le-i1 $e |- B <_ E $.
  ntp4vc-i3-le-i2 $e |- C <_ B $.
  ntp4vc-i3-nonnegative $e |- 0 <_ C $.
  ntp4vc-i3-lt-i2 $e |- C < B $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-x1-nonnegative $e |- 0 <_ ( NTP4VCX1 B C ) $.
  ntp4vc-x3-le-target $e |- (
    ( NTP4VCX3 D A B C ) <_ F
  ) $.
  ntp4vc-x4-nonnegative $e |- 0 <_ ( NTP4VCX4 B C ) $.
  ntp4vc-target-le-x3 $e |- (
    F <_ ( NTP4VCX3 D A B C )
  ) $.

  ntp4vc-i2-overflow-bound $e |- (
    B <_ ( ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 + C )
  ) $.
  ntp4vc-x1-overflow-bound $e |- (
    ( NTP4VCX1 B C ) <_ ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.
  ntp4vc-x4-overflow-bound $e |- (
    ( NTP4VCX4 B C ) <_ ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5
  ) $.

  ntp4vc-linked-allocation $e |- T e. L $.

  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-target-sint32 $e |- ( NTP4VCSint32 F ) $.

  ntp4vc-array-sorted $e |- (
    NTP4VCSorted D A 0 E
  ) $.
  ntp4vc-prefix-strict-upper-bound $e |- (
    NTP4VCStrictUpperBound D A 0 C F
  ) $.
  ntp4vc-suffix-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound D A B E F
  ) $.

  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShiftSint32 A 0 ) E
  ) $.
  ntp4vc-x2-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX2 B C )
  ) $.
  ntp4vc-x3-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX3 D A B C )
  ) $.
  ntp4vc-midpoint-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCA1 A B C ) 1
  ) $.

  ntp4vc-equal-range-call-lower-bound-pre-sorted-goal26 $a |- (
    NTP4VCSorted
      D
      ( NTP4VCShiftSint32 A C )
      0
      ( NTP4VCX1 B C )
  ) $.
$}
