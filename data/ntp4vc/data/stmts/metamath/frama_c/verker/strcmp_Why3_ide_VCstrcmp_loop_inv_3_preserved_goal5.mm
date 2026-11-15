$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_3_preserved_goal5:
  the strcmp loop-invariant preservation condition concludes that the
  successor of the current address lies between the first string address and
  its terminating address, under the generated signed and unsigned integer
  conversions, string-length, string-comparison, address-order,
  memory-validity, linking, constancy, signed-byte, offset-alignment, and
  matched-prefix assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCUint8,
  NTP4VCSint8, NTP4VCSint64, NTP4VCUint64, and NTP4VCValidStr directly
  expand the corresponding source definitions.

  The arbitrary relation J represents addr_le with its source law under equal
  bases retained explicitly. The arbitrary map G and sets H and I represent
  region, linked, and sconst. K, L, O, and P represent to_uint8, to_uint64,
  to_sint8, and to_sint64, while M and N represent l_strlen and
  l_strncmp_1'. Their source range, identity, cross-projection, and
  fixed-point laws, together with the definitions of l_cmp and l_strcmp,
  retain the relevant imported source theory without assigning stronger
  properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  maps, relations, and predicates keep their unrestricted source domains.
  Each valid-string null-position witness remains internally existential.
  Both prefix assumptions retain their full integer quantifiers and
  implication scopes, and the equality of the two source propositions is
  rendered by the equivalent biconditional. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCSint8Limit NTP4VCSint64Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW
  NTP4VCUint8 NTP4VCSint8 NTP4VCSint64 NTP4VCUint64 NTP4VCValidStr
  NTP4VCCmp NTP4VCStrlen NTP4VCStrncmp NTP4VCStrcmp
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint64-limit-class $a class NTP4VCSint64Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-cmp-class $a class ( NTP4VCCmp A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strncmp-class
  $a class ( NTP4VCStrncmp A B C D E ) $.
ntp4vc-strcmp-class
  $a class ( NTP4VCStrcmp A B C D E ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint64-syntax $a wff ( NTP4VCSint64 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-sint64-limit-def $a |- NTP4VCSint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  9 2 2 3 3 7 2 0 3 6 8 5 4 7 7 5 8 0 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-cmp-def $a |- ( NTP4VCCmp A B ) =
  if ( B = A , 0 , if ( A < B , -u 1 , 1 ) ) $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strncmp-def $a |- ( NTP4VCStrncmp A B C D E ) =
  ( A ` <. B , <. C , <. D , E >. >. >. ) $.
ntp4vc-strcmp-def $a |- ( NTP4VCStrcmp A B C D E ) =
  ( NTP4VCStrncmp A C D E ( NTP4VCStrlen B C D ) ) $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
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

ntp4vc-sint64-def $a |- ( ( NTP4VCSint64 A ) <->
  ( -u NTP4VCSint64Limit <_ A /\ A < NTP4VCSint64Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
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
  $d x y z w A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_1, B=a, C=a_2, D=a_3, E=a_1, and F=t.
     G is region; H and I are the linked and sconst extensions; J is the
     addr_le extension; K, L, O, and P are to_uint8, to_uint64, to_sint8,
     and to_sint64; M and N are l_strlen and l_strncmp_1'. Source lets are
     expanded as
       x=A(B), x_1=K(A(B)), x_2=A(C),
       x_3=offset(C), x_4=offset(D), x_5=strlen(A,D),
       x_6=offset(C)-offset(D), x_7=A(shift(D,x_6)),
       x_8=A(shift(E,x_6)), a_4=shift(E,strlen(A,E)), and
       a_5=shift(B,1). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- E e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- I C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- J C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint8-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint64-function $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint8-function $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint64-function $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- M e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strncmp-function $e |- N e.
    (
      ZZ
      ^m
      (
        ( ZZ ^m NTP4VCAddr )
        X.
        ( NTP4VCAddr X. ( NTP4VCAddr X. ZZ ) )
      )
    ) $.

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

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( K ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( L ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( L ` x ) = x
    ) $.

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( O ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
      ->
      ( O ` x ) = x
    ) $.

  ntp4vc-to-sint64-range $e |- A. x e. ZZ
    ( NTP4VCSint64 ( P ` x ) ) $.

  ntp4vc-to-sint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint64 x )
      ->
      ( P ` x ) = x
    ) $.

  ntp4vc-proj-int8 $e |- A. x e. ZZ
    ( ( O ` ( K ` x ) ) = ( O ` x ) ) $.

  ntp4vc-proj-int64 $e |- A. x e. ZZ
    ( ( P ` ( L ` x ) ) = ( P ` x ) ) $.

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
            ( L ` ( 1 + ( NTP4VCStrlen M x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen M x y ) ) $.

  ntp4vc-strncmp-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. NTP4VCAddr
          A. w e. ZZ
            (
              ( NTP4VCStrncmp N x y z w )
              =
              if
              (
                w = -u 1 ,
                0 ,
                if
                (
                  ( x ` ( NTP4VCShift z 0 ) )
                  =
                  ( x ` ( NTP4VCShift y 0 ) ) ,
                  (
                    NTP4VCStrncmp
                      N x
                      ( NTP4VCShift y 1 )
                      ( NTP4VCShift z 1 )
                      ( w - 1 )
                  ) ,
                  (
                    NTP4VCCmp
                      ( K ` ( x ` ( NTP4VCShift y 0 ) ) )
                      ( K ` ( x ` ( NTP4VCShift z 0 ) ) )
                  )
                )
              )
            ) $.

  ntp4vc-current-converted-byte-nonzero $e |- (
    ( K ` ( A ` B ) ) =/= 0
  ) $.

  ntp4vc-next-converted-byte-equality $e |- (
    ( K ` ( A ` C ) ) = ( K ` ( A ` B ) )
  ) $.

  ntp4vc-strcmp-result-equality $e |- (
    ( NTP4VCStrcmp N M A D E )
    =
    ( NTP4VCStrcmp N M A C B )
  ) $.

  ntp4vc-offset-alignment $e |- (
    ( ( NTP4VCOffset E ) + ( NTP4VCOffset C ) )
    =
    ( ( NTP4VCOffset B ) + ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-remaining-length-alignment $e |- (
    ( ( NTP4VCOffset D ) + ( NTP4VCStrlen M A D ) )
    =
    ( ( NTP4VCOffset C ) + ( NTP4VCStrlen M A C ) )
  ) $.

  ntp4vc-shifted-byte-equality $e |- (
    (
      A
      `
      (
        NTP4VCShift
          D
          ( ( NTP4VCOffset C ) - ( NTP4VCOffset D ) )
      )
    )
    =
    (
      A
      `
      (
        NTP4VCShift
          E
          ( ( NTP4VCOffset C ) - ( NTP4VCOffset D ) )
      )
    )
  ) $.

  ntp4vc-converted-raw-prefix-equivalence $e |- (
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x <_ ( NTP4VCStrlen M A D )
          ->
          (
            K ` ( A ` ( NTP4VCShift D x ) )
          )
          =
          (
            K ` ( A ` ( NTP4VCShift E x ) )
          )
        )
      )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x <_ ( NTP4VCStrlen M A D )
          ->
          (
            A ` ( NTP4VCShift D x )
          )
          =
          (
            A ` ( NTP4VCShift E x )
          )
        )
      )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( G ` ( NTP4VCBase E ) ) <_ 0
  ) $.

  ntp4vc-region-a3 $e |- (
    ( G ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-sconst-memory $e |- A e. I $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe J E B ) $.
  ntp4vc-a3-le-a2 $e |- ( NTP4VCAddrLe J D C ) $.
  ntp4vc-current-byte-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a2-byte-sint8 $e |- ( NTP4VCSint8 ( A ` C ) ) $.

  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr F A B ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr F A E ) $.
  ntp4vc-a2-valid-string $e |- ( NTP4VCValidStr F A C ) $.
  ntp4vc-a3-valid-string $e |- ( NTP4VCValidStr F A D ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      J
      B
      ( NTP4VCShift E ( NTP4VCStrlen M A E ) )
  ) $.

  ntp4vc-a2-le-a3-end $e |- (
    NTP4VCAddrLe
      J
      C
      ( NTP4VCShift D ( NTP4VCStrlen M A D ) )
  ) $.

  ntp4vc-shifted-a1-byte-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        (
          NTP4VCShift
            E
            ( ( NTP4VCOffset C ) - ( NTP4VCOffset D ) )
        )
      )
  ) $.

  ntp4vc-shifted-a3-byte-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        (
          NTP4VCShift
            D
            ( ( NTP4VCOffset C ) - ( NTP4VCOffset D ) )
        )
      )
  ) $.

  ntp4vc-matched-prefix-before-a2 $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + ( NTP4VCOffset D ) ) < ( NTP4VCOffset C )
        ->
        (
          A ` ( NTP4VCShift D x )
        )
        =
        (
          A ` ( NTP4VCShift E x )
        )
      )
    ) $.

  ntp4vc-strcmp-loop-inv-3-preserved-goal5 $a |- (
    ( NTP4VCAddrLe J E ( NTP4VCShift B 1 ) )
    /\
    (
      NTP4VCAddrLe
        J
        ( NTP4VCShift B 1 )
        ( NTP4VCShift E ( NTP4VCStrlen M A E ) )
    )
  ) $.
$}
