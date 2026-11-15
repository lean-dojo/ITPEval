$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/strcat_Why3_ide_VCstrcat_call_strcpy_pre_6_goal9:
  the strcat verification condition concludes separation of the destination
  string region from the selected source-address region under the generated
  string-length, memory-validity, initial separation, address-order, linking,
  constancy, signed-byte, and conditional first-null-byte assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCSint8, NTP4VCStringLength, NTP4VCZeroInString, and
  NTP4VCFirstZero directly expand the corresponding source definitions
  specialized to the zero character where the source statement does so.

  The arbitrary integer-valued map K represents region. Membership of the
  allocation map E in the arbitrary set L represents linked, while membership
  of the integer memory B in the arbitrary set M represents sconst. The
  arbitrary relation N represents addr_le, with its source law under equal
  bases retained explicitly. The arbitrary maps O and P respectively
  represent l_length specialized to B and to_sint8; their relevant imported
  source laws are explicit hypotheses. No stronger laws are assigned to these
  uninterpreted source symbols.

  Every source let-binding is expanded at its uses. All address and integer
  parameters keep their original domains, and both the universal no-null
  condition and the existential null-byte condition retain their full integer
  quantifier domains and original implication scopes. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSeparated NTP4VCSint8
  NTP4VCStringLength NTP4VCZeroInString NTP4VCFirstZero
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-string-length-syntax $a wff
  ( NTP4VCStringLength A B C D ) $.
ntp4vc-zero-in-string-syntax $a wff
  ( NTP4VCZeroInString A B C ) $.
ntp4vc-first-zero-syntax $a wff
  ( NTP4VCFirstZero A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A ) $.

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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

${
  $d x A B C D $.
  ntp4vc-string-length-def $a |- (
    ( NTP4VCStringLength A B C D )
    <->
    (
      ( B ` ( NTP4VCShift C D ) ) = 0
      /\
      (
        0 <_ D
        /\
        (
          ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + D ) )
          /\
          A. x e. ZZ
            (
              0 <_ x
              ->
              (
                x < D
                ->
                ( B ` ( NTP4VCShift C x ) ) =/= 0
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d x A B C $.
  ntp4vc-zero-in-string-def $a |- (
    ( NTP4VCZeroInString A B C )
    <->
    E. x e. ZZ
      (
        ( A ` ( NTP4VCShift B x ) ) = 0
        /\
        ( 0 <_ x /\ x < C )
      )
  ) $.
$}

${
  $d x A B C D E F $.
  ntp4vc-first-zero-def $a |- (
    ( NTP4VCFirstZero A B C D E F )
    <->
    (
      ( B ` ( NTP4VCShift C E ) ) = ( F ` 0 )
      /\
      (
        0 <_ E
        /\
        (
          E <_ ( D ` C )
          /\
          (
            -u ; ; 1 2 8 <_ 0
            /\
            (
              0 <_ ; ; 1 2 7
              /\
              (
                ( NTP4VCValidRW A
                    ( NTP4VCShift C 0 ) ( 1 + ( D ` C ) ) )
                /\
                A. x e. ZZ
                  (
                    0 <_ x
                    ->
                    (
                      x < E
                      ->
                      ( B ` ( NTP4VCShift C x ) ) =/= ( F ` 0 )
                    )
                  )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x y A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=a_2, B=t_1, C=a, D=a_1, E=t, F=i, G=i_3, H=i_1,
     I=i_2, and J=i_4.

     K is region; L and M are the linked and sconst extensions; N is the
     addr_le extension; O is l_length specialized to B; and P is to_sint8.
     Source lets are expanded as:
       x=base(A), x_1=B(C), a_3=shift(A,0), x_2=O(D),
       x_3=O(A), a_4=shift(D,0), and x_4=1+O(D). $)

  ntp4vc-a2-address $e |- A e. NTP4VCAddr $.
  ntp4vc-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i3-integer $e |- G e. ZZ $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-i2-integer $e |- I e. ZZ $.
  ntp4vc-i4-integer $e |- J e. ZZ $.

  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- M C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- N C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-length-map $e |- O e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-sint8-function $e |- P e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe N x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-length-law $e |- A. x e. NTP4VCAddr A. y e. ZZ
    (
      ( NTP4VCStringLength E B x y )
      ->
      ( O ` x ) = y
    ) $.

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( P ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
      ->
      ( P ` x ) = x
    ) $.

  ntp4vc-region-a1 $e |- (
    ( K ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-region-a2 $e |- (
    ( K ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. L $.
  ntp4vc-sconst-memory $e |- B e. M $.

  ntp4vc-current-byte-sint8 $e |- (
    NTP4VCSint8 ( B ` C )
  ) $.

  ntp4vc-a1-length-i $e |- (
    NTP4VCStringLength E B D F
  ) $.

  ntp4vc-a1-length-i3 $e |- (
    NTP4VCStringLength E B D G
  ) $.

  ntp4vc-a2-length-i1 $e |- (
    NTP4VCStringLength E B A H
  ) $.

  ntp4vc-a2-length-i2 $e |- (
    NTP4VCStringLength E B A I
  ) $.

  ntp4vc-a2-length-i4 $e |- (
    NTP4VCStringLength E B A J
  ) $.

  ntp4vc-combined-region-valid $e |- (
    NTP4VCValidRW
      E
      ( NTP4VCShift A 0 )
      ( ( O ` D ) + ( O ` A ) )
  ) $.

  ntp4vc-initial-regions-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift A 0 )
      ( 1 + ( O ` A ) )
      ( NTP4VCShift D 0 )
      ( 1 + ( O ` D ) )
  ) $.

  ntp4vc-no-null-implies-null-address $e |- (
    (
      A. x e. ZZ
        (
          0 <_ x
          ->
          (
            x < ( O ` A )
            ->
            ( B ` ( NTP4VCShift A x ) ) =/= 0
          )
        )
    )
    ->
    <. 0 , 0 >. = C
  ) $.

  ntp4vc-null-implies-selected-byte-zero $e |- (
    ( NTP4VCZeroInString B A ( O ` A ) )
    ->
    ( B ` C ) = 0
  ) $.

  ntp4vc-null-implies-same-base $e |- (
    ( NTP4VCZeroInString B A ( O ` A ) )
    ->
    ( NTP4VCBase A ) = ( NTP4VCBase C )
  ) $.

  ntp4vc-null-implies-first-occurrence $e |- (
    ( NTP4VCZeroInString B A ( O ` A ) )
    ->
    (
      NTP4VCFirstZero
        E B A O
        ( ( NTP4VCOffset C ) - ( NTP4VCOffset A ) )
        P
    )
  ) $.

  ntp4vc-null-implies-address-bounds $e |- (
    ( NTP4VCZeroInString B A ( O ` A ) )
    ->
    (
      ( NTP4VCAddrLe N A C )
      /\
      ( NTP4VCAddrLe N C ( NTP4VCShift A ( O ` A ) ) )
    )
  ) $.

  ntp4vc-strcat-call-strcpy-pre-6-goal9 $a |- (
    NTP4VCSeparated
      ( NTP4VCShift D 0 )
      ( 1 + ( O ` D ) )
      ( NTP4VCShift C 0 )
      ( 1 + ( O ` D ) )
  ) $.
$}
