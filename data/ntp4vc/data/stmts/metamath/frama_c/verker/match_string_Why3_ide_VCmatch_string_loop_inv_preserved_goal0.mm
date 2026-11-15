$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_preserved_goal0:
  the match-string loop-invariant preservation condition concludes that the
  current array index is strictly below the real array length and is at least
  negative one, under the generated memory, range, mismatch, valid-string,
  prefix, and comparison assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCFramed,
  NTP4VCValidStr, and the signed and unsigned integer predicates directly
  expand the corresponding source definitions. NTP4VCMin is the ordinary
  integer minimum.

  The arbitrary total functions N and O represent to_uint64 and to_uint8,
  with their source range and identity laws. P, Q, and R represent l_strlen,
  l_strncmp_1', and l_real_len. Their displayed fixed-point and range laws,
  together with the definitions of l_cmp and l_strcmp, retain the relevant
  source theory. The region function and the extensions of linked and sconst
  remain arbitrary.

  Source let-bindings are expanded at every use. The proposition-valued
  comparison conditional is rendered by its equivalent integer-valued
  conditional equality. All quantified indices retain the full integer
  domain, and the existential witness in NTP4VCValidStr remains internal.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint8Limit NTP4VCSint8Limit
  NTP4VCSint32Limit NTP4VCMaxSint32 NTP4VCUint64Limit
  NTP4VCUint8 NTP4VCSint8 NTP4VCSint32 NTP4VCUint64
  NTP4VCValidRW NTP4VCFramed NTP4VCValidStr
  NTP4VCMin NTP4VCCmp NTP4VCStrlen NTP4VCStrncmp
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
ntp4vc-min-class $a class ( NTP4VCMin A B ) $.
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
ntp4vc-min-def $a |- ( NTP4VCMin A B ) =
  if ( A < B , A , B ) $.
ntp4vc-cmp-def $a |- ( NTP4VCCmp A B ) =
  if ( B = A , 0 , if ( A < B , -u 1 , 1 ) ) $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strncmp-def $a |- ( NTP4VCStrncmp A B C D E ) =
  ( A ` <. B , <. C , <. D , E >. >. >. ) $.
ntp4vc-strcmp-def $a |- ( NTP4VCStrcmp A B C D E ) =
  ( NTP4VCStrncmp A C D E ( NTP4VCStrlen B C D ) ) $.
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
  $d x y z w A B C D E F G H I J K L M N O P Q R $.

  $( Source parameters:
     A=t_2, B=a_1, C=i_1, D=t_1, E=a, F=i_2, G=i, H=i_3,
     I=i_4, and J=t. K is region; L and M are the linked and sconst
     extensions; N and O are to_uint64 and to_uint8; P, Q, and R are
     l_strlen, l_strncmp_1', and l_real_len. $)

  ntp4vc-pointer-memory $e |- A e.
    ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- C e. ZZ $.
  ntp4vc-char-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-i3-integer $e |- H e. ZZ $.
  ntp4vc-i4-integer $e |- I e. ZZ $.
  ntp4vc-allocation-map $e |- J e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- M C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-uint64-function $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint8-function $e |- O e. ( ZZ ^m ZZ ) $.

  ntp4vc-strlen-function $e |- P e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strncmp-function $e |- Q e.
    (
      ZZ
      ^m
      (
        ( ZZ ^m NTP4VCAddr )
        X.
        ( NTP4VCAddr X. ( NTP4VCAddr X. ZZ ) )
      )
    ) $.
  ntp4vc-real-len-function $e |- R e.
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
    ( NTP4VCUint64 ( N ` x ) ) $.
  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint64 x ) -> ( N ` x ) = x ) $.
  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( O ` x ) ) $.
  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint8 x ) -> ( O ` x ) = x ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen P x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( N ` ( 1 + ( NTP4VCStrlen P x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.
  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen P x y ) ) $.

  ntp4vc-strncmp-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. NTP4VCAddr
          A. w e. ZZ
            (
              ( NTP4VCStrncmp Q x y z w )
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
                      Q x
                      ( NTP4VCShift y 1 )
                      ( NTP4VCShift z 1 )
                      ( w - 1 )
                  ) ,
                  (
                    NTP4VCCmp
                      ( O ` ( x ` ( NTP4VCShift y 0 ) ) )
                      ( O ` ( x ` ( NTP4VCShift z 0 ) ) )
                  )
                )
              )
            ) $.

  ntp4vc-real-len-fixed-point $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCRealLen R x y z )
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
                N
                `
                (
                  1
                  +
                  (
                    NTP4VCRealLen
                      R x
                      ( NTP4VCShift y 1 )
                      ( N ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.
  ntp4vc-real-len-range $e |-
    A. x e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCRealLen R x y z ) ) $.

  ntp4vc-a2-nonnull $e |- (
    ( A ` ( NTP4VCShift B C ) ) =/= <. 0 , 0 >.
  ) $.
  ntp4vc-strcmp-nonzero $e |- (
    ( NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B C ) ) E ) =/= 0
  ) $.
  ntp4vc-i2-mismatch $e |- (
    (
      D ` ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) F )
    )
    =/=
    ( D ` ( NTP4VCShift E F ) )
  ) $.
  ntp4vc-i3-mismatch $e |- (
    (
      D ` ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) H )
    )
    =/=
    ( D ` ( NTP4VCShift E H ) )
  ) $.
  ntp4vc-i4-mismatch $e |- (
    (
      D ` ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) I )
    )
    =/=
    ( D ` ( NTP4VCShift E I ) )
  ) $.

  ntp4vc-i1-nonnegative $e |- 0 <_ C $.
  ntp4vc-i2-nonnegative $e |- 0 <_ F $.
  ntp4vc-i3-nonnegative $e |- 0 <_ H $.
  ntp4vc-i4-nonnegative $e |- 0 <_ I $.
  ntp4vc-converted-i1-lt-i $e |- ( N ` C ) < G $.
  ntp4vc-region-a $e |- ( K ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( K ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-real-len-le-i $e |- ( NTP4VCRealLen R A B G ) <_ G $.
  ntp4vc-i1-le-real-len $e |- C <_ ( NTP4VCRealLen R A B G ) $.
  ntp4vc-i2-le-strlen-a2 $e |- (
    F <_ ( NTP4VCStrlen P D ( A ` ( NTP4VCShift B C ) ) )
  ) $.
  ntp4vc-i3-le-strlen-a2 $e |- (
    H <_ ( NTP4VCStrlen P D ( A ` ( NTP4VCShift B C ) ) )
  ) $.
  ntp4vc-i4-le-min-length $e |- (
    I
    <_
    (
      NTP4VCMin
        ( NTP4VCStrlen P D E )
        ( NTP4VCStrlen P D ( A ` ( NTP4VCShift B C ) ) )
    )
  ) $.
  ntp4vc-i-le-max-sint32 $e |- G <_ NTP4VCMaxSint32 $.
  ntp4vc-pointer-memory-framed $e |- ( NTP4VCFramed K A ) $.
  ntp4vc-allocation-linked $e |- J e. L $.
  ntp4vc-char-memory-constant $e |- D e. M $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 G ) $.
  ntp4vc-i4-uint64 $e |- ( NTP4VCUint64 I ) $.
  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr J D E ) $.
  ntp4vc-next-i1-sint32 $e |- ( NTP4VCSint32 ( 1 + C ) ) $.
  ntp4vc-a2-valid-string $e |- (
    NTP4VCValidStr J D ( A ` ( NTP4VCShift B C ) )
  ) $.
  ntp4vc-strcmp-sint32 $e |- (
    NTP4VCSint32
      ( NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B C ) ) E )
  ) $.
  ntp4vc-strcmp-sign-from-bytes $e |- (
    (
      NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B C ) ) E
    )
    =
    if
    (
      (
        O ` ( D ` ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) F ) )
      )
      <
      ( O ` ( D ` ( NTP4VCShift E F ) ) ) ,
      -u 1 ,
      1
    )
  ) $.
  ntp4vc-full-length-valid-rw $e |- (
    ( NTP4VCRealLen R A B G ) = G
    ->
    ( NTP4VCValidRW J ( NTP4VCShift B 0 ) G )
  ) $.
  ntp4vc-short-length-valid-rw $e |- (
    ( NTP4VCRealLen R A B G ) < G
    ->
    (
      NTP4VCValidRW
        J
        ( NTP4VCShift B 0 )
        ( 1 + ( NTP4VCRealLen R A B G ) )
    )
  ) $.
  ntp4vc-strcmp-sign $e |- (
    (
      NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B C ) ) E
    )
    =
    -u 1
    \/
    (
      NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B C ) ) E
    )
    =
    1
  ) $.

  ntp4vc-earlier-array-strings-valid $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < C
        ->
        ( NTP4VCValidStr J D ( A ` ( NTP4VCShift B x ) ) )
      )
    ) $.
  ntp4vc-prefix-equal $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < F
        ->
        (
          D ` ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) x )
        )
        =
        ( D ` ( NTP4VCShift E x ) )
      )
    ) $.
  ntp4vc-earlier-array-strings-not-equal $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < C
        ->
        ( NTP4VCStrcmp Q P D ( A ` ( NTP4VCShift B x ) ) E ) =/= 0
      )
    ) $.
  ntp4vc-real-prefix-array-strings-valid $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCRealLen R A B G )
        ->
        (
          ( NTP4VCUint64 x )
          ->
          ( NTP4VCValidStr J D ( A ` ( NTP4VCShift B x ) ) )
        )
      )
    ) $.

  ntp4vc-match-string-loop-inv-preserved-goal0 $a |- (
    C < ( NTP4VCRealLen R A B G )
    /\
    -u 1 <_ C
  ) $.
$}
