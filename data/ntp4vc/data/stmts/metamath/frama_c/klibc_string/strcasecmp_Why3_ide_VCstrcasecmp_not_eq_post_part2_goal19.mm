$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19:
  the strcasecmp verification condition concludes that two strings are not
  case-insensitively equal throughout the address interval preceding a known
  differing byte, under the generated integer, string-length, memory,
  separation, address-order, linking, constancy, and character-case
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCSint32, NTP4VCSint8, NTP4VCUint8, NTP4VCIsLower,
  NTP4VCIsUpper, and NTP4VCStringLength directly expand the corresponding
  source definitions.

  The arbitrary integer-valued map M represents region. Membership of the
  allocation map G in the arbitrary set N represents linked, while membership
  of the integer memory D in the arbitrary set P represents sconst. The
  arbitrary relation Q represents addr_le, with its source law under equal
  bases retained explicitly. The arbitrary maps R, S, and T respectively
  represent l_length specialized to D, to_uint8, and l_toupper. Their relevant
  imported source laws are retained as explicit hypotheses without assigning
  stronger definitions to these uninterpreted functions.

  Every source let-binding is expanded at its uses. Both string-length
  predicates retain their full address and integer domains, and the concluding
  universal byte comparison retains its full integer domain and original
  implication scope. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint32Limit NTP4VCSint8Limit NTP4VCUint8Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSeparated
  NTP4VCSint32 NTP4VCSint8 NTP4VCUint8
  NTP4VCIsLower NTP4VCIsUpper NTP4VCStringLength
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-is-lower-syntax $a wff ( NTP4VCIsLower A ) $.
ntp4vc-is-upper-syntax $a wff ( NTP4VCIsUpper A ) $.
ntp4vc-string-length-syntax $a wff ( NTP4VCStringLength A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-is-lower-def $a |- ( ( NTP4VCIsLower A ) <->
  ( ; 9 7 <_ A /\ A <_ ; ; 1 2 2 )
) $.

ntp4vc-is-upper-def $a |- ( ( NTP4VCIsUpper A ) <->
  ( ; 6 5 <_ A /\ A <_ ; 9 0 )
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
  $d x y z A B C D E F G H I J K L M N P Q R S T $.

  $( Source parameters:
     A=a, B=a_1, C=a_2, D=t_1, E=i_5, F=i_6, G=t, H=i,
     I=i_1, J=i_4, K=i_2, and L=i_3.

     M is region; N and P are the linked and sconst extensions; Q is the
     addr_le extension; R is l_length specialized to D; S is to_uint8; and
     T is l_toupper. Source lets are expanded as:
       x=base(A), x_1=offset(B), x_2=offset(A),
       a_3=shift(C,offset(B)-offset(A)), x_3=D(B),
       x_4=R(A), x_5=R(C), and x_6=S(D(B)). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i5-integer $e |- E e. ZZ $.
  ntp4vc-i6-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- H e. ZZ $.
  ntp4vc-i1-integer $e |- I e. ZZ $.
  ntp4vc-i4-integer $e |- J e. ZZ $.
  ntp4vc-i2-integer $e |- K e. ZZ $.
  ntp4vc-i3-integer $e |- L e. ZZ $.

  ntp4vc-region-map $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- N C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- P C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- Q C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-length-map $e |- R e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-uint8-function $e |- S e. ( ZZ ^m ZZ ) $.
  ntp4vc-toupper-function $e |- T e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe Q x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-length-law $e |- A. x e. NTP4VCAddr A. y e. ZZ
    (
      ( NTP4VCStringLength G D x y )
      ->
      ( R ` x ) = y
    ) $.

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( S ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( S ` x ) = x
    ) $.

  ntp4vc-toupper-range $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( NTP4VCSint8 ( T ` x ) )
    ) $.

  ntp4vc-toupper-character-law $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      (
        ( NTP4VCIsLower x )
        ->
        (
          ( ; 3 2 + ( T ` x ) ) = x
          /\
          A. y e. ZZ
            (
              ( NTP4VCUint8 y )
              ->
              (
                ( NTP4VCIsUpper y )
                ->
                (
                  ( T ` y ) = y
                  /\
                  A. z e. ZZ
                    (
                      ( NTP4VCUint8 z )
                      ->
                      (
                        -. ( NTP4VCIsLower z )
                        ->
                        (
                          -. ( NTP4VCIsUpper z )
                          ->
                          ( T ` z ) = z
                        )
                      )
                    )
                )
              )
            )
        )
      )
    ) $.

  ntp4vc-base-equality $e |- (
    ( NTP4VCBase B ) = ( NTP4VCBase A )
  ) $.

  ntp4vc-known-byte-difference $e |- (
    (
      T
      `
      ( S ` ( D ` ( NTP4VCShift C E ) ) )
    )
    =/=
    (
      T
      `
      ( S ` ( D ` ( NTP4VCShift A E ) ) )
    )
  ) $.

  ntp4vc-shifted-a2-null $e |- (
    (
      D
      `
      ( NTP4VCShift C ( ( NTP4VCOffset B ) - ( NTP4VCOffset A ) ) )
    )
    =
    0
  ) $.

  ntp4vc-i5-nonnegative $e |- 0 <_ E $.
  ntp4vc-i5-le-i6 $e |- E <_ F $.
  ntp4vc-current-byte-nonnegative $e |- 0 <_ ( D ` B ) $.
  ntp4vc-region-a $e |- ( M ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( M ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-current-byte-upper-bound $e |- ( D ` B ) <_ ; ; 2 5 5 $.

  ntp4vc-linked-allocation $e |- G e. N $.
  ntp4vc-sconst-memory $e |- D e. P $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-a-le-a1 $e |- ( NTP4VCAddrLe Q A B ) $.
  ntp4vc-current-byte-sint8 $e |- ( NTP4VCSint8 ( D ` B ) ) $.

  ntp4vc-a-length-i1 $e |- ( NTP4VCStringLength G D A I ) $.
  ntp4vc-a-length-i4 $e |- ( NTP4VCStringLength G D A J ) $.
  ntp4vc-a-length-i6 $e |- ( NTP4VCStringLength G D A F ) $.
  ntp4vc-a2-length-i2 $e |- ( NTP4VCStringLength G D C K ) $.
  ntp4vc-a2-length-i3 $e |- ( NTP4VCStringLength G D C L ) $.
  ntp4vc-a2-length-i6 $e |- ( NTP4VCStringLength G D C F ) $.

  ntp4vc-a1-le-a-end $e |- (
    NTP4VCAddrLe Q B ( NTP4VCShift A ( R ` A ) )
  ) $.

  ntp4vc-strings-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift C 0 ) ( 1 + ( R ` C ) )
      ( NTP4VCShift A 0 ) ( 1 + ( R ` A ) )
  ) $.

  ntp4vc-a2-le-shifted-a2 $e |- (
    NTP4VCAddrLe
      Q
      C
      ( NTP4VCShift C ( ( NTP4VCOffset B ) - ( NTP4VCOffset A ) ) )
  ) $.

  ntp4vc-shifted-a2-le-a2-end $e |- (
    NTP4VCAddrLe
      Q
      ( NTP4VCShift C ( ( NTP4VCOffset B ) - ( NTP4VCOffset A ) ) )
      ( NTP4VCShift C ( R ` C ) )
  ) $.

  ntp4vc-lower-zero-case $e |- (
    ( NTP4VCIsLower 0 )
    ->
    H = -u ; 3 2
  ) $.

  ntp4vc-upper-zero-case $e |- (
    ( NTP4VCIsUpper 0 )
    ->
    H = 0
  ) $.

  ntp4vc-neither-zero-case $e |- (
    -. ( NTP4VCIsLower 0 )
    ->
    (
      -. ( NTP4VCIsUpper 0 )
      ->
      H = 0
    )
  ) $.

  ntp4vc-current-upper-case $e |- (
    ( NTP4VCIsUpper ( S ` ( D ` B ) ) )
    ->
    ( D ` B ) = H
  ) $.

  ntp4vc-current-lower-case $e |- (
    ( NTP4VCIsLower ( S ` ( D ` B ) ) )
    ->
    ( D ` B ) = ( ; 3 2 + H )
  ) $.

  ntp4vc-current-neither-case $e |- (
    -. ( NTP4VCIsLower ( S ` ( D ` B ) ) )
    ->
    (
      -. ( NTP4VCIsUpper ( S ` ( D ` B ) ) )
      ->
      ( D ` B ) = H
    )
  ) $.

  ntp4vc-strcasecmp-not-eq-post-part2-goal19 $a |- -.
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          ( x + ( NTP4VCOffset A ) ) < ( NTP4VCOffset B )
          ->
          (
            T
            `
            ( S ` ( D ` ( NTP4VCShift C x ) ) )
          )
          =
          (
            T
            `
            ( S ` ( D ` ( NTP4VCShift A x ) ) )
          )
        )
      ) $.
$}
