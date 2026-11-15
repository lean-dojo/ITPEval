$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/x509_parser/parse_generalizedTime_Why3_ide_VCparse_generalizedTime_call_compute_decimal_pre_part1_5_goal32:
  the generalized-time decimal-conversion precondition verification condition
  concludes that the byte at offset fourteen is at least the ASCII digit
  lower bound 48, under the generated address-distinctness, fixed-byte,
  integer-range, region, linking, memory-validity, separation, unsigned-width,
  and quantified digit assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint8, NTP4VCUint16,
  NTP4VCValidRW, NTP4VCValidRD, and NTP4VCSeparated directly expand the
  corresponding source definitions.

  In the scoped statement A is a_7; B is t_1; C, D, E, F, G, H, and I are
  a_1, a, a_2, a_3, a_4, a_5, and a_6; J, K, L, M, N, O, and P are i,
  i_2, i_3, i_4, i_5, i_6, and i_1; and Q is t. R is the arbitrary
  integer-valued region map, while membership of Q in the arbitrary set S
  represents linked t. Thus the source's uninterpreted region and linked
  symbols receive no additional laws.

  Every source let-binding is expanded at its use. All addresses, integers,
  maps, and predicates retain their unrestricted source domains. The final
  digit hypothesis retains its full integer quantifier and curried
  implication scope. Splitting the source implication chain into scoped
  hypotheses is bidirectionally equivalent for these arbitrary parameters.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCUint16Limit
  NTP4VCUint8 NTP4VCUint16
  NTP4VCValidRW NTP4VCValidRD NTP4VCSeparated
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
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.

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

ntp4vc-separated-def $a |- ( ( NTP4VCSeparated A B C D ) <->
  (
    B <_ 0
    \/
    (
      D <_ 0
      \/
      (
        ( NTP4VCBase A ) =/= ( NTP4VCBase C )
        \/
        (
          ( ( NTP4VCOffset C ) + D ) <_ ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCOffset C )
        )
      )
    )
  )
) $.

${
  $d x A B C D E F G H I J K L M N O P Q R S $.

  $( Source parameters and uninterpreted imported symbols are mapped as
     described above. Source lets expand to shifts of A at offsets zero
     through sixteen, and byte reads apply B to those addresses. $)

  ntp4vc-a7-address $e |- A e. NTP4VCAddr $.
  ntp4vc-byte-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- E e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- F e. NTP4VCAddr $.
  ntp4vc-a4-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a5-address $e |- H e. NTP4VCAddr $.
  ntp4vc-a6-address $e |- I e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- J e. ZZ $.
  ntp4vc-i2-integer $e |- K e. ZZ $.
  ntp4vc-i3-integer $e |- L e. ZZ $.
  ntp4vc-i4-integer $e |- M e. ZZ $.
  ntp4vc-i5-integer $e |- N e. ZZ $.
  ntp4vc-i6-integer $e |- O e. ZZ $.
  ntp4vc-i1-integer $e |- P e. ZZ $.
  ntp4vc-allocation-map $e |- Q e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- S C_ ( ZZ ^m ZZ ) $.

  ntp4vc-a1-ne-a $e |- C =/= D $.
  ntp4vc-a2-ne-a $e |- E =/= D $.
  ntp4vc-a2-ne-a1 $e |- E =/= C $.
  ntp4vc-a3-ne-a $e |- F =/= D $.
  ntp4vc-a3-ne-a1 $e |- F =/= C $.
  ntp4vc-a3-ne-a2 $e |- F =/= E $.
  ntp4vc-a4-ne-a $e |- G =/= D $.
  ntp4vc-a4-ne-a1 $e |- G =/= C $.
  ntp4vc-a4-ne-a2 $e |- G =/= E $.
  ntp4vc-a4-ne-a3 $e |- G =/= F $.
  ntp4vc-a5-ne-a $e |- H =/= D $.
  ntp4vc-a5-ne-a1 $e |- H =/= C $.
  ntp4vc-a5-ne-a2 $e |- H =/= E $.
  ntp4vc-a5-ne-a3 $e |- H =/= F $.
  ntp4vc-a5-ne-a4 $e |- H =/= G $.
  ntp4vc-a6-ne-a $e |- I =/= D $.
  ntp4vc-a6-ne-a1 $e |- I =/= C $.
  ntp4vc-a6-ne-a2 $e |- I =/= E $.
  ntp4vc-a6-ne-a3 $e |- I =/= F $.
  ntp4vc-a6-ne-a4 $e |- I =/= G $.
  ntp4vc-a6-ne-a5 $e |- I =/= H $.

  ntp4vc-a7-nonnull $e |- <. 0 , 0 >. =/= A $.
  ntp4vc-offset-zero-byte $e |- (
    B ` ( NTP4VCShift A 0 )
  ) = ; 2 4 $.
  ntp4vc-offset-one-byte $e |- (
    B ` ( NTP4VCShift A 1 )
  ) = ; 1 5 $.
  ntp4vc-offset-sixteen-byte $e |- (
    B ` ( NTP4VCShift A ; 1 6 )
  ) = ; 9 0 $.

  ntp4vc-i-nonnegative $e |- 0 <_ J $.
  ntp4vc-i2-nonnegative $e |- 0 <_ K $.
  ntp4vc-i3-nonnegative $e |- 0 <_ L $.
  ntp4vc-i4-nonnegative $e |- 0 <_ M $.
  ntp4vc-i5-nonnegative $e |- 0 <_ N $.
  ntp4vc-i6-nonnegative $e |- 0 <_ O $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( R ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( R ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( R ` ( NTP4VCBase F ) ) <_ 0 $.
  ntp4vc-region-a4 $e |- ( R ` ( NTP4VCBase G ) ) <_ 0 $.
  ntp4vc-region-a5 $e |- ( R ` ( NTP4VCBase H ) ) <_ 0 $.
  ntp4vc-region-a6 $e |- ( R ` ( NTP4VCBase I ) ) <_ 0 $.
  ntp4vc-region-a7 $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-fourteen-le-i1 $e |- ; 1 4 <_ P $.
  ntp4vc-seventeen-le-i $e |- ; 1 7 <_ J $.
  ntp4vc-i3-le-99 $e |- L <_ ; 9 9 $.
  ntp4vc-i4-le-99 $e |- M <_ ; 9 9 $.
  ntp4vc-i5-le-99 $e |- N <_ ; 9 9 $.
  ntp4vc-i6-le-99 $e |- O <_ ; 9 9 $.
  ntp4vc-i2-le-9999 $e |- K <_ ; ; ; 9 9 9 9 $.

  ntp4vc-offset-two-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 2 ) ) $.
  ntp4vc-offset-three-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 3 ) ) $.
  ntp4vc-offset-four-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 4 ) ) $.
  ntp4vc-offset-five-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 5 ) ) $.
  ntp4vc-offset-six-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 6 ) ) $.
  ntp4vc-offset-seven-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 7 ) ) $.
  ntp4vc-offset-eight-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 8 ) ) $.
  ntp4vc-offset-nine-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A 9 ) ) $.
  ntp4vc-offset-ten-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A ; 1 0 ) ) $.
  ntp4vc-offset-eleven-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A ; 1 1 ) ) $.
  ntp4vc-offset-twelve-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A ; 1 2 ) ) $.
  ntp4vc-offset-thirteen-lower-digit $e |- ; 4 8 <_
    ( B ` ( NTP4VCShift A ; 1 3 ) ) $.

  ntp4vc-offset-two-upper-digit $e |-
    ( B ` ( NTP4VCShift A 2 ) ) <_ ; 5 7 $.
  ntp4vc-offset-three-upper-digit $e |-
    ( B ` ( NTP4VCShift A 3 ) ) <_ ; 5 7 $.
  ntp4vc-offset-four-upper-digit $e |-
    ( B ` ( NTP4VCShift A 4 ) ) <_ ; 5 7 $.
  ntp4vc-offset-five-upper-digit $e |-
    ( B ` ( NTP4VCShift A 5 ) ) <_ ; 5 7 $.
  ntp4vc-offset-six-upper-digit $e |-
    ( B ` ( NTP4VCShift A 6 ) ) <_ ; 5 7 $.
  ntp4vc-offset-seven-upper-digit $e |-
    ( B ` ( NTP4VCShift A 7 ) ) <_ ; 5 7 $.
  ntp4vc-offset-eight-upper-digit $e |-
    ( B ` ( NTP4VCShift A 8 ) ) <_ ; 5 7 $.
  ntp4vc-offset-nine-upper-digit $e |-
    ( B ` ( NTP4VCShift A 9 ) ) <_ ; 5 7 $.
  ntp4vc-offset-ten-upper-digit $e |-
    ( B ` ( NTP4VCShift A ; 1 0 ) ) <_ ; 5 7 $.
  ntp4vc-offset-eleven-upper-digit $e |-
    ( B ` ( NTP4VCShift A ; 1 1 ) ) <_ ; 5 7 $.
  ntp4vc-offset-twelve-upper-digit $e |-
    ( B ` ( NTP4VCShift A ; 1 2 ) ) <_ ; 5 7 $.
  ntp4vc-offset-thirteen-upper-digit $e |-
    ( B ` ( NTP4VCShift A ; 1 3 ) ) <_ ; 5 7 $.

  ntp4vc-linked-allocation $e |- Q e. S $.
  ntp4vc-i1-uint8 $e |- ( NTP4VCUint8 P ) $.
  ntp4vc-i3-uint8 $e |- ( NTP4VCUint8 L ) $.
  ntp4vc-i4-uint8 $e |- ( NTP4VCUint8 M ) $.
  ntp4vc-i5-uint8 $e |- ( NTP4VCUint8 N ) $.
  ntp4vc-i6-uint8 $e |- ( NTP4VCUint8 O ) $.
  ntp4vc-i-uint16 $e |- ( NTP4VCUint16 J ) $.
  ntp4vc-i2-uint16 $e |- ( NTP4VCUint16 K ) $.

  ntp4vc-a-valid-rw $e |- ( NTP4VCValidRW Q D 1 ) $.
  ntp4vc-a1-valid-rw $e |- ( NTP4VCValidRW Q C 1 ) $.
  ntp4vc-a2-valid-rw $e |- ( NTP4VCValidRW Q E 1 ) $.
  ntp4vc-a3-valid-rw $e |- ( NTP4VCValidRW Q F 1 ) $.
  ntp4vc-a4-valid-rw $e |- ( NTP4VCValidRW Q G 1 ) $.
  ntp4vc-a5-valid-rw $e |- ( NTP4VCValidRW Q H 1 ) $.
  ntp4vc-a6-valid-rw $e |- ( NTP4VCValidRW Q I 1 ) $.

  ntp4vc-offset-two-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 2 ) )
  ) $.
  ntp4vc-offset-three-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 3 ) )
  ) $.
  ntp4vc-offset-four-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 4 ) )
  ) $.
  ntp4vc-offset-five-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 5 ) )
  ) $.
  ntp4vc-offset-six-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 6 ) )
  ) $.
  ntp4vc-offset-seven-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 7 ) )
  ) $.
  ntp4vc-offset-eight-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 8 ) )
  ) $.
  ntp4vc-offset-nine-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A 9 ) )
  ) $.
  ntp4vc-offset-ten-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 0 ) )
  ) $.
  ntp4vc-offset-eleven-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 1 ) )
  ) $.
  ntp4vc-offset-twelve-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 2 ) )
  ) $.
  ntp4vc-offset-thirteen-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 3 ) )
  ) $.
  ntp4vc-offset-fourteen-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 4 ) )
  ) $.
  ntp4vc-offset-fifteen-uint8 $e |- (
    NTP4VCUint8 ( B ` ( NTP4VCShift A ; 1 5 ) )
  ) $.

  ntp4vc-offset-zero-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 0 ) 1
  ) $.
  ntp4vc-offset-one-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 1 ) 1
  ) $.
  ntp4vc-offset-two-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 2 ) 1
  ) $.
  ntp4vc-offset-three-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 3 ) 1
  ) $.
  ntp4vc-offset-four-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 4 ) 1
  ) $.
  ntp4vc-offset-five-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 5 ) 1
  ) $.
  ntp4vc-offset-six-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 6 ) 1
  ) $.
  ntp4vc-offset-seven-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 7 ) 1
  ) $.
  ntp4vc-offset-eight-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 8 ) 1
  ) $.
  ntp4vc-offset-nine-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A 9 ) 1
  ) $.
  ntp4vc-offset-ten-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 0 ) 1
  ) $.
  ntp4vc-offset-eleven-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 1 ) 1
  ) $.
  ntp4vc-offset-twelve-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 2 ) 1
  ) $.
  ntp4vc-offset-thirteen-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 3 ) 1
  ) $.
  ntp4vc-offset-fourteen-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 4 ) 1
  ) $.
  ntp4vc-offset-fifteen-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 5 ) 1
  ) $.
  ntp4vc-offset-sixteen-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ; 1 6 ) 1
  ) $.

  ntp4vc-a-separated $e |- (
    NTP4VCSeparated D 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a1-separated $e |- (
    NTP4VCSeparated C 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a2-separated $e |- (
    NTP4VCSeparated E 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a3-separated $e |- (
    NTP4VCSeparated F 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a4-separated $e |- (
    NTP4VCSeparated G 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a5-separated $e |- (
    NTP4VCSeparated H 1 ( NTP4VCShift A 0 ) J
  ) $.
  ntp4vc-a6-separated $e |- (
    NTP4VCSeparated I 1 ( NTP4VCShift A 0 ) J
  ) $.

  ntp4vc-end-offset-valid-rd $e |- (
    NTP4VCValidRD Q ( NTP4VCShift A ( 2 + P ) ) 1
  ) $.
  ntp4vc-positive-prefix-valid-rd $e |- (
    0 < J
    ->
    ( NTP4VCValidRD Q ( NTP4VCShift A 0 ) J )
  ) $.

  ntp4vc-quantified-digits $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < P
        ->
        (
          ; 4 8 <_ ( B ` ( NTP4VCShift A ( 2 + x ) ) )
          /\
          ( B ` ( NTP4VCShift A ( 2 + x ) ) ) <_ ; 5 7
        )
      )
    ) $.

  ntp4vc-parse-generalizedtime-compute-decimal-pre-part1-5-goal32 $a |- (
    ; 4 8 <_ ( B ` ( NTP4VCShift A ; 1 4 ) )
  ) $.
$}
