$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/strndup_Why3_ide_VCstrndup_call_memcpy_pre_4_goal5:
  the strndup verification condition concludes writable validity of the
  destination region for length i_1 under the generated nonnull, converted
  size, integer-range, source-memory, linking, constancy, region, and
  zero-byte case assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, and NTP4VCUint32 directly
  expand the corresponding source definitions.

  The arbitrary integer-valued map H represents region. Membership of the
  allocation map E in the arbitrary set I represents linked, while membership
  of the integer memory F in the arbitrary set J represents sconst. The
  arbitrary map K represents to_uint32; its relevant imported range and
  identity laws are retained explicitly without assigning stronger behavior
  to it.

  The source let-bindings are expanded as x = K(1 + A) and
  a_2 = shift(B,0). All address and integer parameters keep their original
  domains. The universal no-zero-byte condition and existential zero-byte
  condition retain their full integer quantifier domains and implication
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCValidRW NTP4VCUint32
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

${
  $d x A B C D E F H I J K $.

  $( Source parameters:
     A=i_1, B=a, C=a_1, D=i, E=t, and F=t_1.
     H is region; I and J are the linked and sconst extensions; K is
     to_uint32. Source lets are expanded as x=K(1+A) and
     a_2=shift(B,0). $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-uint32-function $e |- K e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( K ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-a1-nonnull $e |- C =/= <. 0 , 0 >. $.

  ntp4vc-converted-size-nonzero $e |- (
    ( K ` ( 1 + A ) ) =/= 0
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ D $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. I $.
  ntp4vc-sconst-memory $e |- F e. J $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.

  ntp4vc-source-valid-rw $e |- (
    NTP4VCValidRW E ( NTP4VCShift B 0 ) D
  ) $.

  ntp4vc-destination-valid-if-positive $e |- (
    0 < ( K ` ( 1 + A ) )
    ->
    (
      NTP4VCValidRW
        E
        ( NTP4VCShift C 0 )
        ( K ` ( 1 + A ) )
    )
  ) $.

  ntp4vc-no-zero-implies-equal-length $e |- (
    (
      A. x e. ZZ
        (
          0 <_ x
          ->
          (
            x < D
            ->
            ( F ` ( NTP4VCShift B x ) ) =/= 0
          )
        )
    )
    ->
    A = D
  ) $.

  ntp4vc-zero-implies-length-bound $e |- (
    (
      E. x e. ZZ
        (
          ( F ` ( NTP4VCShift B x ) ) = 0
          /\
          ( 0 <_ x /\ x < D )
        )
    )
    ->
    A <_ D
  ) $.

  ntp4vc-strndup-call-memcpy-pre-4-goal5 $a |- (
    NTP4VCValidRW E ( NTP4VCShift B 0 ) A
  ) $.
$}
