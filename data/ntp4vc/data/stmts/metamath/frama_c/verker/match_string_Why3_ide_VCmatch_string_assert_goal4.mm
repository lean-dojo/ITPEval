$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_assert_goal4: the
  match-string verification condition concludes that the nonnull string
  selected at the current array index is valid, under the generated memory,
  integer-range, writable-region, and valid-prefix assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCFramed,
  NTP4VCValidStr, and the signed and unsigned integer predicates directly
  expand the corresponding source definitions.

  The arbitrary total functions K and L represent to_uint64 and to_uint8,
  with their source range and identity laws. M, N, and O represent l_strlen,
  l_strncmp_1', and l_real_len. Their displayed fixed-point and range laws,
  together with the definitions of l_cmp and l_strcmp, are exactly the
  relevant source axioms. The region function and the extensions of linked
  and sconst remain arbitrary.

  Source let-bindings are expanded at every use. All quantified indices retain
  the full integer domain, and the existential witness in NTP4VCValidStr
  remains internal. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCSint8Limit
  NTP4VCSint32Limit NTP4VCMaxSint32 NTP4VCUint64Limit
  NTP4VCUint8 NTP4VCSint8 NTP4VCSint32 NTP4VCUint64
  NTP4VCValidRW NTP4VCFramed NTP4VCValidStr
  NTP4VCCmp NTP4VCStrlen NTP4VCStrncmp
  NTP4VCStrcmp NTP4VCRealLen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
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
ntp4vc-real-len-class
  $a class ( NTP4VCRealLen A B C D ) $.

ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-valid-str-syntax
  $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
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
  (
    NTP4VCStrncmp
      A C D E
      ( NTP4VCStrlen B C D )
  ) $.

ntp4vc-real-len-def $a |- ( NTP4VCRealLen A B C D ) =
  ( A ` <. B , <. C , D >. >. ) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
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

${
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

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
  $d x y z w A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=t_2, B=a_1, C=i_1, D=i, E=a, F=t, and G=t_1.
     H is region; I and J are the linked and sconst extensions; K and L are
     to_uint64 and to_uint8; M, N, and O are l_strlen, l_strncmp_1', and
     l_real_len. $)

  ntp4vc-pointer-memory $e |- A e.
    ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- C e. ZZ $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-char-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-to-uint64-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint8-function $e |- L e. ( ZZ ^m ZZ ) $.

  ntp4vc-strlen-function $e |- M e.
    (
      ZZ
      ^m
      ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr )
    ) $.

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

  ntp4vc-real-len-function $e |- O e.
    (
      ZZ
      ^m
      (
        ( NTP4VCAddr ^m NTP4VCAddr )
        X.
        ( NTP4VCAddr X. ZZ )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( K ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( L ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( L ` x ) = x
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
            (
              K
              `
              (
                1
                +
                ( NTP4VCStrlen M x ( NTP4VCShift y 1 ) )
              )
            )
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
                  (
                    x ` ( NTP4VCShift z 0 )
                  )
                  =
                  (
                    x ` ( NTP4VCShift y 0 )
                  ) ,
                  (
                    NTP4VCStrncmp
                      N x
                      ( NTP4VCShift y 1 )
                      ( NTP4VCShift z 1 )
                      ( w - 1 )
                  ) ,
                  (
                    NTP4VCCmp
                      ( L ` ( x ` ( NTP4VCShift y 0 ) ) )
                      ( L ` ( x ` ( NTP4VCShift z 0 ) ) )
                  )
                )
              )
            ) $.

  ntp4vc-real-len-fixed-point $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCRealLen O x y z )
            =
            if
            (
              (
                z = 0
                \/
                ( x ` ( NTP4VCShift y 0 ) ) = <. 0 , 0 >.
              ) ,
              0 ,
              (
                K
                `
                (
                  1
                  +
                  (
                    NTP4VCRealLen
                      O x
                      ( NTP4VCShift y 1 )
                      ( K ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-real-len-range $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCRealLen O x y z ) ) $.

  ntp4vc-a2-nonnull $e |- (
    ( A ` ( NTP4VCShift B C ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-i1-nonnegative $e |- 0 <_ C $.

  ntp4vc-converted-i1-lt-i $e |- ( K ` C ) < D $.

  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase E ) ) <_ 0 $.

  ntp4vc-region-a1 $e |- ( H ` ( NTP4VCBase B ) ) <_ 0 $.

  ntp4vc-real-len-le-i $e |- (
    ( NTP4VCRealLen O A B D ) <_ D
  ) $.

  ntp4vc-i1-le-real-len $e |- (
    C <_ ( NTP4VCRealLen O A B D )
  ) $.

  ntp4vc-i-le-max-sint32 $e |- D <_ NTP4VCMaxSint32 $.

  ntp4vc-pointer-memory-framed $e |- ( NTP4VCFramed H A ) $.

  ntp4vc-allocation-linked $e |- F e. I $.

  ntp4vc-char-memory-constant $e |- G e. J $.

  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 C ) $.

  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 D ) $.

  ntp4vc-a-valid-string $e |- (
    NTP4VCValidStr F G E
  ) $.

  ntp4vc-full-length-valid-rw $e |- (
    ( NTP4VCRealLen O A B D ) = D
    ->
    ( NTP4VCValidRW F ( NTP4VCShift B 0 ) D )
  ) $.

  ntp4vc-short-length-valid-rw $e |- (
    ( NTP4VCRealLen O A B D ) < D
    ->
    (
      NTP4VCValidRW
        F
        ( NTP4VCShift B 0 )
        ( 1 + ( NTP4VCRealLen O A B D ) )
    )
  ) $.

  ntp4vc-earlier-array-strings-valid $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < C
        ->
        (
          NTP4VCValidStr
            F G ( A ` ( NTP4VCShift B x ) )
        )
      )
    ) $.

  ntp4vc-earlier-array-strings-not-equal $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < C
        ->
        (
          NTP4VCStrcmp
            N M G
            ( A ` ( NTP4VCShift B x ) )
            E
        )
        =/=
        0
      )
    ) $.

  ntp4vc-real-prefix-array-strings-valid $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCRealLen O A B D )
        ->
        (
          ( NTP4VCUint64 x )
          ->
          (
            NTP4VCValidStr
              F G ( A ` ( NTP4VCShift B x ) )
          )
        )
      )
    ) $.

  ntp4vc-match-string-assert-goal4 $a |- (
    NTP4VCValidStr
      F G ( A ` ( NTP4VCShift B C ) )
  ) $.
$}
