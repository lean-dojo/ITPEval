$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/x509_parser/check_utf8_string_Why3_ide_VCcheck_utf8_string_assert_rte_mem_access_9_part03_goal29:
  the check-UTF-8-string memory-access verification condition concludes that
  one byte is readable at address a_1 shifted by three, under the generated
  nonzero, address, UTF-8 byte-pattern, region, linking, integer-width, and
  prior read-validity assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint8, NTP4VCUint16, and
  NTP4VCValidRD directly expand the corresponding source definitions.
  NTP4VCLand192Eq128 is the exact integer bit condition for
  land(192,x)=128: bit 7 is set and bit 6 is clear, expressed by floor
  quotient modulo two.

  In the scoped statement A, B, C, D, E, and F represent a_1, a, i, i_1, t,
  and t_1. G is region, and membership of E in the arbitrary set H represents
  linked t, so the imported uninterpreted symbols receive no extra laws. The
  source lets a_2=shift(a_1,0), a_3=shift(a_1,1), x=t_1(a_3),
  a_4=shift(a_1,2), x_1=t_1(a_4), and a_5=shift(a_1,3) are expanded at every
  use. Splitting the source curried implication chain into essential
  hypotheses is bidirectionally equivalent for these arbitrary parameters.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCUint16Limit
  NTP4VCUint8 NTP4VCUint16 NTP4VCValidRD
  NTP4VCLand192Eq128
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.

ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-uint16-syntax $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-land-192-eq-128-syntax $a wff ( NTP4VCLand192Eq128 A ) $.

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

ntp4vc-land-192-eq-128-def $a |- (
  ( NTP4VCLand192Eq128 A )
  <->
  (
    ( ( ( |_ ` ( A / ( 2 ^ 7 ) ) ) mod 2 ) = 1 )
    /\
    ( ( ( |_ ` ( A / ( 2 ^ 6 ) ) ) mod 2 ) = 0 )
  )
) $.

${
  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-byte-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonzero $e |- C =/= 0 $.
  ntp4vc-i1-nonzero $e |- D =/= 0 $.
  ntp4vc-a-nonnull $e |- <. 0 , 0 >. =/= B $.

  ntp4vc-first-byte-244 $e |- (
    F ` ( NTP4VCShift A 0 )
  ) = ; ; 2 4 4 $.
  ntp4vc-second-byte-pattern $e |- (
    NTP4VCLand192Eq128 ( F ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-third-byte-pattern $e |- (
    NTP4VCLand192Eq128 ( F ` ( NTP4VCShift A 2 ) )
  ) $.

  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-four-le-i $e |- 4 <_ C $.
  ntp4vc-128-le-second-byte $e |- ; ; 1 2 8 <_ (
    F ` ( NTP4VCShift A 1 )
  ) $.
  ntp4vc-second-byte-le-143 $e |- (
    F ` ( NTP4VCShift A 1 )
  ) <_ ; ; 1 4 3 $.

  ntp4vc-linked-allocation $e |- E e. H $.
  ntp4vc-i-uint16 $e |- ( NTP4VCUint16 C ) $.
  ntp4vc-i1-uint16 $e |- ( NTP4VCUint16 D ) $.
  ntp4vc-second-byte-uint8 $e |- (
    NTP4VCUint8 ( F ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-third-byte-uint8 $e |- (
    NTP4VCUint8 ( F ` ( NTP4VCShift A 2 ) )
  ) $.
  ntp4vc-fourth-byte-uint8 $e |- (
    NTP4VCUint8 ( F ` ( NTP4VCShift A 3 ) )
  ) $.

  ntp4vc-a2-one-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift A 0 ) 1
  ) $.
  ntp4vc-a2-i-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift A 0 ) C
  ) $.
  ntp4vc-a3-one-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift A 1 ) 1
  ) $.
  ntp4vc-a4-one-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift A 2 ) 1
  ) $.
  ntp4vc-a-prefix-valid-rd $e |- (
    0 < D
    ->
    ( NTP4VCValidRD E ( NTP4VCShift B 0 ) D )
  ) $.

  ntp4vc-check-utf8-string-mem-access-9-part03-goal29 $a |- (
    NTP4VCValidRD E ( NTP4VCShift A 3 ) 1
  ) $.
$}
