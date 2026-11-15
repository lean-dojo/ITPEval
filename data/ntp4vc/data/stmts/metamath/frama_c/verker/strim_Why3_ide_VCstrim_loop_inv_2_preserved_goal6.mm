$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strim_Why3_ide_VCstrim_loop_inv_2_preserved_goal6: the
  string-trimming loop-invariant preservation condition concludes that the
  byte at the post-state address a_2 is whitespace, under the generated
  string-length, address-order, memory-validity, linking, constancy,
  integer-range, non-null, and intervening-whitespace assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCUint8,
  NTP4VCSint8, NTP4VCUint64, NTP4VCValidStr, and NTP4VCIsSpace directly
  expand the corresponding source definitions.

  The arbitrary relations K and L represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map H and
  sets I and J represent region, linked, and sconst. M and N represent
  l_strlen and to_uint64; their source fixed-point, range, and identity laws
  are retained as explicit hypotheses without assigning stronger properties
  to these symbols.

  All four source let-bindings are expanded at every use. All addresses,
  integers, maps, relations, and predicates retain their unrestricted source
  domains. The valid-string null-position witness remains internally
  existential, and both universal assumptions retain their full integer or
  address domains and implication scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCUint8 NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr NTP4VCIsSpace
  NTP4VCStrlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-is-space-syntax $a wff ( NTP4VCIsSpace A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
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

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
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
  $d x y A B C D E F H I J K L M N $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, D=i, E=t, and F=a_2.
     H is region; I and J are the linked and sconst extensions; K and L are
     the addr_le and addr_lt extensions; M is l_strlen; and N is to_uint64.
     Source lets are expanded as
       x=NTP4VCStrlen(M,A,B),
       a_3=NTP4VCShift(B,x-1),
       x_1=A(a_3), and x_2=A(C). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-a2-address $e |- F e. NTP4VCAddr $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- K C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- L C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- M e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-to-uint64-function $e |- N e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe K x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt L x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( N ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( N ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen M x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( N ` ( 1 + ( NTP4VCStrlen M x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen M x y ) ) $.

  ntp4vc-i-nonzero $e |- D =/= 0 $.

  ntp4vc-length-nonzero $e |- (
    ( NTP4VCStrlen M A B ) =/= 0
  ) $.

  ntp4vc-end-null $e |- (
    (
      A
      `
      ( NTP4VCShift B ( NTP4VCStrlen M A B ) )
    )
    =
    0
  ) $.

  ntp4vc-last-byte-nonzero $e |- (
    (
      A
      `
      ( NTP4VCShift B ( ( NTP4VCStrlen M A B ) - 1 ) )
    )
    =/=
    0
  ) $.

  ntp4vc-length-positive $e |- (
    0 < ( NTP4VCStrlen M A B )
  ) $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. I $.
  ntp4vc-sconst-memory $e |- A e. J $.
  ntp4vc-i-uint8 $e |- ( NTP4VCUint8 D ) $.
  ntp4vc-a-le-a1 $e |- ( NTP4VCAddrLe K B C ) $.
  ntp4vc-a1-byte-sint8 $e |- ( NTP4VCSint8 ( A ` C ) ) $.
  ntp4vc-a1-byte-whitespace $e |- ( NTP4VCIsSpace ( A ` C ) ) $.
  ntp4vc-valid-string $e |- ( NTP4VCValidStr E A B ) $.
  ntp4vc-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrlen M A B )
  ) $.

  ntp4vc-before-a1-lt-a2 $e |- (
    NTP4VCAddrLt L ( NTP4VCShift C ( -u 1 ) ) F
  ) $.

  ntp4vc-before-a-le-a1 $e |- (
    NTP4VCAddrLe K ( NTP4VCShift B ( -u 1 ) ) C
  ) $.

  ntp4vc-a1-le-last-address $e |- (
    NTP4VCAddrLe
      K
      C
      ( NTP4VCShift B ( ( NTP4VCStrlen M A B ) - 1 ) )
  ) $.

  ntp4vc-a2-le-last-address $e |- (
    NTP4VCAddrLe
      K
      F
      ( NTP4VCShift B ( ( NTP4VCStrlen M A B ) - 1 ) )
  ) $.

  ntp4vc-last-byte-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        ( NTP4VCShift B ( ( NTP4VCStrlen M A B ) - 1 ) )
      )
  ) $.

  ntp4vc-no-null-before-end $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrlen M A B )
        ->
        ( A ` ( NTP4VCShift B x ) ) =/= 0
      )
    ) $.

  ntp4vc-intervening-whitespace $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt L C x )
      ->
      (
        (
          NTP4VCAddrLe
            K
            x
            ( NTP4VCShift B ( ( NTP4VCStrlen M A B ) - 1 ) )
        )
        ->
        ( NTP4VCIsSpace ( A ` x ) )
      )
    ) $.

  ntp4vc-strim-loop-inv-2-preserved-goal6 $a |- (
    NTP4VCIsSpace ( A ` F )
  ) $.
$}
