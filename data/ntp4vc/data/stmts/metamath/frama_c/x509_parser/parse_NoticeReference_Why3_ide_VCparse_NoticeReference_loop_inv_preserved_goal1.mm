$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/x509_parser/parse_NoticeReference_Why3_ide_VCparse_NoticeReference_loop_inv_preserved_goal1:
  the NoticeReference parsing loop-invariant verification condition concludes
  that the remaining suffix of the second input region is readable, under the
  generated address, integer-range, region, linking, unsigned-16, write-
  validity, and guarded prefix-read assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint16, NTP4VCValidRW, and
  NTP4VCValidRD directly expand the corresponding source definitions.

  In the scoped statement A, B, C, D, E, F, G, H, I, J, and K represent
  a_1, a, i_4, i_5, i, i_1, i_2, i_3, a_2, i_6, and t. L is the arbitrary
  integer-valued region map, while membership of K in the arbitrary set M
  represents linked t. Thus the source's uninterpreted region and linked
  symbols receive no additional laws. The source let-bound values are
  expanded at every use:
    x=base(a_1), x_1=base(a), a_3=shift(a_1,i_4),
    a_4=shift(a_1,i_4+i_5-i), x_3=i_4+i_5, x_4=i_1-i_2.
  Splitting the source curried implication chain into the displayed essential
  hypotheses is bidirectionally equivalent for these arbitrary parameters.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxUint16 NTP4VCUint16Limit
  NTP4VCMaxSint32 NTP4VCSint32Limit
  NTP4VCUint16 NTP4VCValidRW NTP4VCValidRD
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-max-uint16-class $a class NTP4VCMaxUint16 $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.

ntp4vc-uint16-syntax $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-max-uint16-def $a |- NTP4VCMaxUint16 =
  ; ; ; ; 6 5 5 3 5 $.
ntp4vc-uint16-limit-def $a |- NTP4VCUint16Limit =
  ; ; ; ; 6 5 5 3 6 $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-uint16-def $a |- ( ( NTP4VCUint16 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint16Limit )
) $.

ntp4vc-valid-rw-def $a |- ( ( NTP4VCValidRW A B C ) <->
  (
    0 < C
    ->
    (
      0 < ( NTP4VCBase B )
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
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

${
  $( Source parameters:
     A=a_1, B=a, C=i_4, D=i_5, E=i, F=i_1, G=i_2, H=i_3,
     I=a_2, J=i_6, K=t, L=region, M=the extension of linked. $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i4-integer $e |- C e. ZZ $.
  ntp4vc-i5-integer $e |- D e. ZZ $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-i2-integer $e |- G e. ZZ $.
  ntp4vc-i3-integer $e |- H e. ZZ $.
  ntp4vc-a2-address $e |- I e. NTP4VCAddr $.
  ntp4vc-i6-integer $e |- J e. ZZ $.
  ntp4vc-allocation-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- M C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonzero $e |- E =/= 0 $.
  ntp4vc-i1-nonzero $e |- F =/= 0 $.
  ntp4vc-i3-nonzero $e |- H =/= 0 $.
  ntp4vc-i5-nonzero $e |- D =/= 0 $.
  ntp4vc-a1-nonnull $e |- <. 0 , 0 >. =/= A $.
  ntp4vc-a2-nonnull $e |- <. 0 , 0 >. =/= I $.
  ntp4vc-a1-base-ne-a-base $e |-
    ( NTP4VCBase A ) =/= ( NTP4VCBase B ) $.
  ntp4vc-a3-nonnull $e |- (
    NTP4VCShift A C
  ) =/= <. 0 , 0 >. $.
  ntp4vc-a4-nonnull $e |- (
    NTP4VCShift A ( ( C + D ) - E )
  ) =/= <. 0 , 0 >. $.

  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i6-le-i $e |- J <_ E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-i2-le-i1 $e |- G <_ F $.
  ntp4vc-i3-nonnegative $e |- 0 <_ H $.
  ntp4vc-i4-le-i3 $e |- C <_ H $.
  ntp4vc-i5-le-i3 $e |- D <_ H $.
  ntp4vc-i5-nonnegative $e |- 0 <_ D $.
  ntp4vc-i6-nonnegative $e |- 0 <_ J $.
  ntp4vc-i4-plus-i5-le-i3 $e |- ( C + D ) <_ H $.
  ntp4vc-i4-plus-i5-nonnegative $e |- 0 <_ ( C + D ) $.

  ntp4vc-region-a $e |- ( L ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( L ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-sint32-lower-i $e |- -u NTP4VCSint32Limit <_ E $.
  ntp4vc-sint32-lower-i6 $e |- -u NTP4VCSint32Limit <_ J $.
  ntp4vc-two-le-i4 $e |- 2 <_ C $.
  ntp4vc-three-le-i2 $e |- 3 <_ G $.
  ntp4vc-i-le-max-uint16 $e |- E <_ NTP4VCMaxUint16 $.
  ntp4vc-i6-le-max-uint16 $e |- J <_ NTP4VCMaxUint16 $.
  ntp4vc-i-le-max-sint32 $e |- E <_ NTP4VCMaxSint32 $.
  ntp4vc-i6-le-max-sint32 $e |- J <_ NTP4VCMaxSint32 $.
  ntp4vc-sint32-lower-i4-plus-i5 $e |-
    -u NTP4VCSint32Limit <_ ( C + D ) $.
  ntp4vc-i4-plus-i5-le-max-uint16 $e |-
    ( C + D ) <_ NTP4VCMaxUint16 $.
  ntp4vc-i4-plus-i5-le-max-sint32 $e |-
    ( C + D ) <_ NTP4VCMaxSint32 $.
  ntp4vc-two-plus-i6-le-i $e |- ( 2 + J ) <_ E $.
  ntp4vc-i1-le-max-uint16-plus-i2 $e |-
    F <_ ( NTP4VCMaxUint16 + G ) $.
  ntp4vc-i1-le-max-sint32-plus-i2 $e |-
    F <_ ( NTP4VCMaxSint32 + G ) $.
  ntp4vc-i2-le-sint32-limit-plus-i1 $e |-
    G <_ ( NTP4VCSint32Limit + F ) $.

  ntp4vc-linked-allocation $e |- K e. M $.
  ntp4vc-i-uint16 $e |- ( NTP4VCUint16 E ) $.
  ntp4vc-i1-uint16 $e |- ( NTP4VCUint16 F ) $.
  ntp4vc-i2-uint16 $e |- ( NTP4VCUint16 G ) $.
  ntp4vc-i3-uint16 $e |- ( NTP4VCUint16 H ) $.
  ntp4vc-i4-uint16 $e |- ( NTP4VCUint16 C ) $.
  ntp4vc-i5-uint16 $e |- ( NTP4VCUint16 D ) $.
  ntp4vc-i6-uint16 $e |- ( NTP4VCUint16 J ) $.
  ntp4vc-a-valid-rw $e |- ( NTP4VCValidRW K B 1 ) $.
  ntp4vc-i-minus-i6-uint16 $e |- (
    NTP4VCUint16 ( E - J )
  ) $.
  ntp4vc-i1-minus-i2-uint16 $e |- (
    NTP4VCUint16 ( F - G )
  ) $.
  ntp4vc-i5-minus-i-uint16 $e |- (
    NTP4VCUint16 ( D - E )
  ) $.

  ntp4vc-a2-prefix-valid-rd $e |- (
    NTP4VCValidRD K ( NTP4VCShift I 0 ) F
  ) $.
  ntp4vc-a1-prefix-valid-rd $e |- (
    0 < H
    ->
    ( NTP4VCValidRD K ( NTP4VCShift A 0 ) H )
  ) $.
  ntp4vc-a3-prefix-valid-rd $e |- (
    0 < D
    ->
    ( NTP4VCValidRD K ( NTP4VCShift A C ) D )
  ) $.
  ntp4vc-a4-prefix-valid-rd $e |- (
    0 < E
    ->
    (
      NTP4VCValidRD
        K
        ( NTP4VCShift A ( ( C + D ) - E ) )
        E
    )
  ) $.

  ntp4vc-parse-notice-reference-loop-inv-preserved-goal1 $a |- (
    NTP4VCValidRD K ( NTP4VCShift I G ) ( F - G )
  ) $.
$}
