$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_goal10: the strchr
  existence-post verification condition concludes that the returned address
  lies between the start of the searched string and its computed terminating
  address, under the generated character-conversion, string-search,
  address-order, memory-validity, linking, constancy, integer-range, branch,
  and no-earlier-match assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCSint32, NTP4VCUint64, and NTP4VCValidStr directly expand the
  corresponding source definitions.

  The arbitrary relations K and L represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map H and
  sets I and J represent region, linked, and sconst. M and N represent
  to_sint8 and to_uint64, while O and P represent l_strlen and l_strchr; their
  source range, identity, and fixed-point laws are retained as explicit
  hypotheses without assigning stronger properties to these symbols.

  All four source let-bindings are expanded at every use. The source
  proposition-valued conditional is rendered by the equivalent disjunction
  of its equality-guarded and disequality-guarded branches. All addresses,
  integers, functions, relations, and predicates retain their unrestricted
  source domains. The existential null-position witnesses in both
  valid-string assumptions remain internal, and the no-earlier-match
  assumption retains its full address quantifier and implication scope. The
  final declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCSint32Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCSint8 NTP4VCSint32 NTP4VCUint64 NTP4VCValidStr
  NTP4VCStrlen NTP4VCStrchr
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strchr-class $a class ( NTP4VCStrchr A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strchr-def $a |- ( NTP4VCStrchr A B C D ) =
  ( A ` <. B , <. C , D >. >. ) $.

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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
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
  $d x y z A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_1, B=a_3, C=a, D=a_1, E=a_2, F=i, and G=t.
     H is region; I and J are the linked and sconst extensions; K and L are
     the addr_le and addr_lt extensions; M and N are to_sint8 and to_uint64;
     O and P are l_strlen and l_strchr. Source lets are expanded as
       x=A(B), x_1=A(C), x_2=A(D), and
       a_4=shift(E,l_strlen(A,E)). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- K C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- L C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-sint8-function $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint64-function $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- O e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strchr-function $e |- P e.
    (
      NTP4VCAddr
      ^m
      (
        ( ZZ ^m NTP4VCAddr )
        X.
        ( NTP4VCAddr X. ZZ )
      )
    ) $.

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

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( M ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
      ->
      ( M ` x ) = x
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
          ( NTP4VCStrlen O x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( N ` ( 1 + ( NTP4VCStrlen O x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen O x y ) ) $.

  ntp4vc-strchr-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrchr P x y z )
            =
            if
            (
              ( x ` y ) = z ,
              y ,
              if
              (
                ( x ` y ) = 0 ,
                <. 0 , 0 >. ,
                ( NTP4VCStrchr P x ( NTP4VCShift y 1 ) z )
              )
            )
          ) $.

  ntp4vc-candidate-value-conversion $e |- (
    ( A ` B ) = ( M ` F )
  ) $.

  ntp4vc-strchr-result-equality $e |- (
    ( NTP4VCStrchr P A E ( A ` B ) )
    =
    ( NTP4VCStrchr P A D ( A ` B ) )
  ) $.

  ntp4vc-region-a2 $e |- (
    ( H ` ( NTP4VCBase E ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- G e. I $.
  ntp4vc-sconst-memory $e |- A e. J $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-a2-le-a1 $e |- ( NTP4VCAddrLe K E D ) $.
  ntp4vc-a2-le-a3 $e |- ( NTP4VCAddrLe K E B ) $.
  ntp4vc-a-value-sint8 $e |- ( NTP4VCSint8 ( A ` C ) ) $.
  ntp4vc-a1-value-sint8 $e |- ( NTP4VCSint8 ( A ` D ) ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr G A D ) $.
  ntp4vc-a2-valid-string $e |- ( NTP4VCValidStr G A E ) $.

  ntp4vc-a1-le-a2-end $e |- (
    NTP4VCAddrLe
      K
      D
      ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
  ) $.

  ntp4vc-a3-le-a2-end $e |- (
    NTP4VCAddrLe
      K
      B
      ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
  ) $.

  ntp4vc-result-branch $e |- (
    (
      ( A ` B ) = ( A ` D )
      /\
      (
        D = C
        /\
        (
          (
            ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
            =
            C
            <->
            ( A ` C ) = 0
          )
          /\
          (
            (
              NTP4VCAddrLt
                L
                C
                ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
            )
            <->
            ( A ` C ) =/= 0
          )
        )
      )
    )
    \/
    (
      ( A ` B ) =/= ( A ` D )
      /\
      (
        <. 0 , 0 >. = C
        /\
        ( A ` D ) = 0
      )
    )
  ) $.

  ntp4vc-no-earlier-match $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt L x D )
      ->
      (
        ( NTP4VCAddrLe K E x )
        ->
        ( A ` B ) =/= ( A ` x )
      )
    ) $.

  ntp4vc-strchr-exists-post-goal10 $a |- (
    ( NTP4VCAddrLe K E C )
    /\
    (
      NTP4VCAddrLe
        K
        C
        ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
    )
  ) $.
$}
