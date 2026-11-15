$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/find_next_bit_0_Why3_ide_VCfind_next_bit_0_assert_rte_mem_access_goal3:
  the find-next-bit verification condition establishes one-unit read validity
  at the address shifted by the current index, under the generated index
  bounds, integer-width conditions, memory validity, region, linking, byte
  value, and zero-prefix assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCUint32, and
  NTP4VCUint8 directly expand the corresponding source definitions.

  The arbitrary integer-valued map G represents region. Membership of the
  allocation map D in the arbitrary set H represents linked, so this imported
  uninterpreted predicate receives no extra laws. I represents l_size,
  including its imported positive signed-32 bound. The source let-bound
  address a_1 is expanded as NTP4VCShift A B at every use. Splitting the
  source implication chain into displayed hypotheses is bidirectionally
  equivalent to the original curried implication, and the quantified prefix
  condition retains its full integer domain. The final declaration is
  Metamath's native unproved $a statement encoding; this database adds no $p
  proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCUint32 NTP4VCUint8
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-uint8-syntax
  $a wff ( NTP4VCUint8 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

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

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

${
  $d x A B C D E F G H I $.

  $( Source parameters:
     A=a, B=i_2, C=i, D=t, E=t_1, and F=i_1.
     G is region, H is the extension of linked, and I is l_size.
     The source let a_1=shift(A,B) is expanded at every use. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- B e. ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-allocation-map $e |- D e. ( ZZ ^m ZZ ) $.
  ntp4vc-byte-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- I e. ZZ $.

  ntp4vc-size-properties $e |- (
    0 < I
    /\
    I <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-i2-lt-i $e |- B < C $.
  ntp4vc-i1-le-i2 $e |- F <_ B $.
  ntp4vc-i-le-size $e |- C <_ I $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- D e. H $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-current-byte-uint8 $e |- (
    NTP4VCUint8 ( E ` ( NTP4VCShift A B ) )
  ) $.

  ntp4vc-prefix-valid-rd $e |- (
    NTP4VCValidRD D ( NTP4VCShift A 0 ) C
  ) $.

  ntp4vc-zero-prefix $e |- A. x e. ZZ
    (
      F <_ x
      ->
      (
        x < B
        ->
        ( E ` ( NTP4VCShift A x ) ) = 0
      )
    ) $.

  ntp4vc-find-next-bit-assert-rte-mem-access-goal3 $a |- (
    NTP4VCValidRD D ( NTP4VCShift A B ) 1
  ) $.
$}
