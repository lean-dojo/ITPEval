$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/x509_parser/get_length_Why3_ide_VCget_length_assert_rte_mem_access_4_goal14:
  the get-length memory-access verification condition concludes that one byte
  is readable at address a_1 shifted by two, under the generated nonzero,
  address-separation, byte-pattern, region, linking, integer-width, write-
  validity, and prefix-read assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint8, NTP4VCUint16,
  NTP4VCValidRW, and NTP4VCValidRD directly expand the corresponding source
  definitions. NTP4VCLand127Eq2 is the exact integer bit condition
  land(127,x)=2, expressed as the low seven-bit residue x mod 128 = 2.
  NTP4VCBitTest gives the exact integer-bit semantics: bit k is set precisely
  when floor division by 2^k has odd remainder.

  In the scoped statement A, B, C, D, E, and F represent a_1, a, a_2, t_1,
  i, and t. G is region, and membership of F in the arbitrary set H
  represents linked t, so the imported uninterpreted symbols receive no extra
  laws. The source lets x=base(a_1), x_1=base(a), x_2=base(a_2),
  a_3=shift(a_1,0), and x_3=t_1(a_3) are expanded at every use. Splitting
  the source curried implication chain into essential hypotheses is
  bidirectionally equivalent for these arbitrary parameters. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCUint16Limit
  NTP4VCUint8 NTP4VCUint16 NTP4VCValidRW NTP4VCValidRD
  NTP4VCLand127Eq2 NTP4VCBitTest
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.

ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-uint16-syntax $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-land-127-eq-2-syntax $a wff ( NTP4VCLand127Eq2 A ) $.
ntp4vc-bit-test-syntax $a wff ( NTP4VCBitTest A B ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-uint16-limit-def $a |- NTP4VCUint16Limit =
  ; ; ; ; 6 5 5 3 6 $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.
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

ntp4vc-land-127-eq-2-def $a |- (
  ( NTP4VCLand127Eq2 A )
  <->
  ( ( A mod ; ; 1 2 8 ) = 2 )
) $.

ntp4vc-bit-test-def $a |- ( ( NTP4VCBitTest A B ) <->
  ( ( ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2 ) = 1 )
) $.

${
  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-byte-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonzero $e |- E =/= 0 $.
  ntp4vc-a2-ne-a $e |- C =/= B $.
  ntp4vc-a1-nonnull $e |- <. 0 , 0 >. =/= A $.
  ntp4vc-a1-base-ne-a-base $e |-
    ( NTP4VCBase A ) =/= ( NTP4VCBase B ) $.
  ntp4vc-a2-base-ne-a1-base $e |-
    ( NTP4VCBase C ) =/= ( NTP4VCBase A ) $.
  ntp4vc-byte-ne-128 $e |- (
    D ` ( NTP4VCShift A 0 )
  ) =/= ; ; 1 2 8 $.
  ntp4vc-byte-low-seven-bits $e |- (
    NTP4VCLand127Eq2 ( D ` ( NTP4VCShift A 0 ) )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( G ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-three-le-i $e |- 3 <_ E $.

  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-i-uint16 $e |- ( NTP4VCUint16 E ) $.
  ntp4vc-a-valid-rw $e |- ( NTP4VCValidRW F B 1 ) $.
  ntp4vc-a2-valid-rw $e |- ( NTP4VCValidRW F C 1 ) $.
  ntp4vc-byte-uint8 $e |- (
    NTP4VCUint8 ( D ` ( NTP4VCShift A 0 ) )
  ) $.
  ntp4vc-byte-high-bit $e |- (
    NTP4VCBitTest ( D ` ( NTP4VCShift A 0 ) ) 7
  ) $.

  ntp4vc-a3-one-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCShift A 0 ) 1
  ) $.
  ntp4vc-a3-prefix-valid-rd $e |- (
    0 < E
    ->
    ( NTP4VCValidRD F ( NTP4VCShift A 0 ) E )
  ) $.

  ntp4vc-get-length-mem-access-4-goal14 $a |- (
    NTP4VCValidRD F ( NTP4VCShift A 2 ) 1
  ) $.
$}
