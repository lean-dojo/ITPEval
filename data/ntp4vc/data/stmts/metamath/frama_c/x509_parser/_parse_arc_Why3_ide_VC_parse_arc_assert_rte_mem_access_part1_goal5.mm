$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/x509_parser/_parse_arc_Why3_ide_VC_parse_arc_assert_rte_mem_access_part1_goal5:
  the parse-arc memory-access verification condition states that one byte is
  readable at address a_1 shifted by i, under the generated address
  separation, integer-range, region, linking, bit-shift, bit-test, write
  validity, and prefix-read assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. NTP4VCBase,
  NTP4VCOffset, NTP4VCShift, NTP4VCUint16, NTP4VCUint32,
  NTP4VCValidRW, and NTP4VCValidRD directly expand the corresponding source
  definitions. Binary left shift is retained as a total integer function on
  ordered integer pairs. NTP4VCBitTest gives the exact integer-bit semantics:
  bit k is set precisely when floor division by 2^k has odd remainder. The
  displayed Cbits laws preserve the imported behavior of left shift and
  conversion against this definition.

  In the scoped statement A, B, and C are a_1, a, and a_2; D, E, and F are
  i_1, i, and i_2; G and H are t and t_1. I is region, J is the extension of
  linked, K is to_uint32, and L is lsl. Splitting the source curried
  implication chain into essential hypotheses is bidirectionally equivalent
  for these arbitrary parameters. The final declaration is Metamath's native
  unproved $a statement encoding; there is no $p proof.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint16Limit NTP4VCUint32Limit NTP4VCUint16 NTP4VCUint32
  NTP4VCValidRW NTP4VCValidRD NTP4VCLsl NTP4VCBitTest
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-lsl-class $a class ( NTP4VCLsl A B C ) $.

ntp4vc-uint16-syntax $a wff ( NTP4VCUint16 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-bit-test-syntax $a wff ( NTP4VCBitTest A B ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-uint16-limit-def $a |- NTP4VCUint16Limit =
  ; ; ; ; 6 5 5 3 6 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-uint16-def $a |- ( ( NTP4VCUint16 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint16Limit )
) $.
ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
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

ntp4vc-lsl-def $a |- ( NTP4VCLsl A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-bit-test-def $a |- ( ( NTP4VCBitTest A B ) <->
  ( ( ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2 ) = 1 )
) $.

${
  $d x y z L $.
  $d x K $.  $d y K $.  $d z K $.
  $d x A $.  $d x E $.  $d x H $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( K ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( K ` x ) = x ) $.

  ntp4vc-lsl-zero $e |- A. x e. ZZ
    ( NTP4VCLsl L x 0 ) = x $.
  ntp4vc-lsl-one $e |- A. x e. ZZ
    ( NTP4VCLsl L x 1 ) = ( 2 x. x ) $.
  ntp4vc-lsl-add $e |- A. x e. ZZ A. y e. ZZ A. z e. ZZ
    (
      ( 0 <_ x /\ 0 <_ y )
      ->
      ( NTP4VCLsl L ( NTP4VCLsl L z x ) y )
      =
      ( NTP4VCLsl L z ( x + y ) )
    ) $.

  ntp4vc-lsl-extraction-low $e |- A. x e. ZZ A. y e. ZZ A. z e. ZZ
    (
      ( ( 0 <_ x /\ 0 <_ y ) /\ y < x )
      ->
      -. ( NTP4VCBitTest ( NTP4VCLsl L z x ) y )
    ) $.
  ntp4vc-lsl-extraction-high $e |- A. x e. ZZ A. y e. ZZ A. z e. ZZ
    (
      ( ( 0 <_ x /\ 0 <_ y ) /\ x <_ y )
      ->
      (
        ( NTP4VCBitTest ( NTP4VCLsl L z x ) y )
        <->
        ( NTP4VCBitTest z ( y - x ) )
      )
    ) $.
  ntp4vc-lsl-one-extraction $e |- A. x e. ZZ A. y e. ZZ
    (
      ( 0 <_ x /\ 0 <_ y )
      ->
      (
        ( NTP4VCBitTest ( NTP4VCLsl L 1 x ) y )
        <->
        x = y
      )
    ) $.
  ntp4vc-to-uint32-extraction-low $e |- A. x e. ZZ A. y e. ZZ
    (
      ( 0 <_ y /\ y < ; 3 2 )
      ->
      (
        ( NTP4VCBitTest ( K ` x ) y )
        <->
        ( NTP4VCBitTest x y )
      )
    ) $.
  ntp4vc-to-uint32-extraction-high $e |- A. x e. ZZ A. y e. ZZ
    (
      ( ( NTP4VCUint32 x ) /\ ; 3 2 <_ y )
      ->
      -. ( NTP4VCBitTest x y )
    ) $.

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-memory-map $e |- H e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-lsl-map $e |- L e. ( ZZ ^m ( ZZ X. ZZ ) ) $.

  ntp4vc-i1-nonzero $e |- D =/= 0 $.
  ntp4vc-a2-ne-a $e |- C =/= B $.
  ntp4vc-a1-nonnull $e |- <. 0 , 0 >. =/= A $.
  ntp4vc-a1-base-ne-a-base $e |-
    ( NTP4VCBase A ) =/= ( NTP4VCBase B ) $.
  ntp4vc-a2-base-ne-a1-base $e |-
    ( NTP4VCBase C ) =/= ( NTP4VCBase A ) $.
  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( I ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( I ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-i2-lt-shift-bound $e |- F <
    ( NTP4VCLsl L 1 ( K ` ( 7 x. E ) ) ) $.
  ntp4vc-i-le-three $e |- E <_ 3 $.
  ntp4vc-i-le-four $e |- E <_ 4 $.
  ntp4vc-five-le-i1 $e |- 5 <_ D $.
  ntp4vc-shift-i2-seven-upper $e |-
    ( NTP4VCLsl L F 7 ) <_
    ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 $.
  ntp4vc-linked-allocation $e |- G e. J $.
  ntp4vc-i-uint16 $e |- ( NTP4VCUint16 E ) $.
  ntp4vc-i1-uint16 $e |- ( NTP4VCUint16 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-a-valid-rw $e |- ( NTP4VCValidRW G B 1 ) $.
  ntp4vc-a2-valid-rw $e |- ( NTP4VCValidRW G C 1 ) $.
  ntp4vc-a1-prefix-valid-rd $e |- (
    0 < D
    ->
    ( NTP4VCValidRD G ( NTP4VCShift A 0 ) D )
  ) $.
  ntp4vc-a1-prefix-high-bit $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < E
        ->
        ( NTP4VCBitTest ( H ` ( NTP4VCShift A x ) ) 7 )
      )
    ) $.

  ntp4vc-parse-arc-mem-access-part1-goal5 $a |- (
    NTP4VCValidRD G ( NTP4VCShift A E ) 1
  ) $.
$}
