$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_len_assign_normal_part7_goal21: the
  string-trimming verification condition concludes that the one-byte region
  immediately after the current scan address is included in the string's
  allocated region through its computed terminator, under the generated
  string-length, address-order, memory-validity, linking, constancy,
  integer-range, non-null, conditional whitespace, and intervening-whitespace
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCIncluded, NTP4VCValidRW,
  NTP4VCInvalid, NTP4VCSint8, NTP4VCUint64, NTP4VCValidStr, and
  NTP4VCIsSpace directly expand the corresponding source definitions.

  The arbitrary relations J and K represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map G and
  sets H and I represent region, linked, and sconst. L represents l_strlen,
  while P represents to_uint64; their fixed-point, range, and identity laws
  retain the relevant imported source theory without assigning stronger
  properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  maps, relations, and predicates keep their original unrestricted domains.
  The valid-string null-position witness remains internally existential, and
  both quantified assumptions retain their full integer or address domains
  and implication scopes. The proposition-valued conditional is rendered by
  its equivalent positive- and negative-case implications. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCIncluded NTP4VCValidRW NTP4VCInvalid
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr NTP4VCIsSpace
  NTP4VCStrlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-included-syntax $a wff ( NTP4VCIncluded A B C D ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-invalid-syntax $a wff ( NTP4VCInvalid A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-is-space-syntax $a wff ( NTP4VCIsSpace A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A
) $.

ntp4vc-addr-lt-def $a |- ( ( NTP4VCAddrLt A B C ) <->
  <. B , C >. e. A
) $.

ntp4vc-included-def $a |- ( ( NTP4VCIncluded A B C D ) <->
  (
    0 < B
    ->
    (
      0 <_ D
      /\
      (
        ( NTP4VCBase A ) = ( NTP4VCBase C )
        /\
        (
          ( NTP4VCOffset C ) <_ ( NTP4VCOffset A )
          /\
          (
            ( ( NTP4VCOffset A ) + B )
            <_
            ( ( NTP4VCOffset C ) + D )
          )
        )
      )
    )
  )
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

ntp4vc-invalid-def $a |- ( ( NTP4VCInvalid A B C ) <->
  (
    0 < C
    ->
    (
      ( A ` ( NTP4VCBase B ) ) <_ ( NTP4VCOffset B )
      \/
      ( ( NTP4VCOffset B ) + C ) <_ 0
    )
  )
) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

ntp4vc-is-space-def $a |- ( ( NTP4VCIsSpace A ) <->
  (
    (
      (
        ( A = 9 \/ A = ; 1 0 )
        \/
        A = ; 1 2
      )
      \/
      A = ; 1 3
    )
    \/
    A = ; 3 2
  )
) $.

${
  $d x y A B C $.
  ntp4vc-valid-str-def $a |- ( ( NTP4VCValidStr A B C ) <->
    E. x e. ZZ
      (
        ( B ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          ( NTP4VCUint64 x )
          /\
          (
            ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + x ) )
            /\
            A. y e. ZZ
              (
                y <_ x
                ->
                ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
              )
          )
        )
      )
  ) $.
$}

${
  $d x y A B D E F G H I J K L P $.

  $( Source parameters:
     A=t_1, B=a, D=a_1, E=t, and F=p.
     G is region; H and I are the linked and sconst extensions; J and K are
     the addr_le and addr_lt extensions; L is l_strlen; and P is to_uint64.
     Source lets are expanded as
       x=NTP4VCStrlen(L,A,B),
       a_2=NTP4VCShift(B,x-1),
       x_1=A(a_2), x_2=A(D), a_3=NTP4VCShift(B,-1), and
       a_4=NTP4VCShift(D,1). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-p-boolean $e |- F e. 2o $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- I C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- J C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- K C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- L e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-to-uint64-function $e |- P e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe J x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt K x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( P ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( P ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen L x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( P ` ( 1 + ( NTP4VCStrlen L x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen L x y ) ) $.

  ntp4vc-length-nonzero $e |- (
    ( NTP4VCStrlen L A B ) =/= 0
  ) $.

  ntp4vc-end-null $e |- (
    (
      A
      `
      ( NTP4VCShift B ( NTP4VCStrlen L A B ) )
    )
    =
    0
  ) $.

  ntp4vc-previous-byte-nonzero $e |- (
    (
      A
      `
      ( NTP4VCShift B ( ( NTP4VCStrlen L A B ) - 1 ) )
    )
    =/=
    0
  ) $.

  ntp4vc-length-positive $e |- (
    0 < ( NTP4VCStrlen L A B )
  ) $.

  ntp4vc-region-a $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. H $.
  ntp4vc-sconst-memory $e |- A e. I $.

  ntp4vc-a1-byte-sint8 $e |- (
    NTP4VCSint8 ( A ` D )
  ) $.

  ntp4vc-valid-string $e |- (
    NTP4VCValidStr E A B
  ) $.

  ntp4vc-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrlen L A B )
  ) $.

  ntp4vc-previous-address-le-a1 $e |- (
    NTP4VCAddrLe J ( NTP4VCShift B ( -u 1 ) ) D
  ) $.

  ntp4vc-a1-successor-not-invalid $e |- (
    -. ( NTP4VCInvalid E ( NTP4VCShift D 1 ) 1 )
  ) $.

  ntp4vc-a1-le-last-address $e |- (
    NTP4VCAddrLe
      J
      D
      ( NTP4VCShift B ( ( NTP4VCStrlen L A B ) - 1 ) )
  ) $.

  ntp4vc-previous-byte-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        ( NTP4VCShift B ( ( NTP4VCStrlen L A B ) - 1 ) )
      )
  ) $.

  ntp4vc-conditional-whitespace-state $e |- (
    (
      ( NTP4VCAddrLe J B D )
      ->
      (
        F = 0
        /\
        -. ( NTP4VCIsSpace ( A ` D ) )
      )
    )
    /\
    (
      -. ( NTP4VCAddrLe J B D )
      ->
      (
        ( NTP4VCShift B ( -u 1 ) ) = D
        \/
        -. ( NTP4VCIsSpace ( A ` D ) )
      )
    )
  ) $.

  ntp4vc-no-null-before-end $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrlen L A B )
        ->
        ( A ` ( NTP4VCShift B x ) ) =/= 0
      )
    ) $.

  ntp4vc-intervening-whitespace $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt K D x )
      ->
      (
        (
          NTP4VCAddrLe
            J
            x
            ( NTP4VCShift B ( ( NTP4VCStrlen L A B ) - 1 ) )
        )
        ->
        ( NTP4VCIsSpace ( A ` x ) )
      )
    ) $.

  ntp4vc-strim-len-assign-normal-part7-goal21 $a |- (
    NTP4VCIncluded
      ( NTP4VCShift D 1 )
      1
      ( NTP4VCShift B 0 )
      ( 1 + ( NTP4VCStrlen L A B ) )
  ) $.
$}
