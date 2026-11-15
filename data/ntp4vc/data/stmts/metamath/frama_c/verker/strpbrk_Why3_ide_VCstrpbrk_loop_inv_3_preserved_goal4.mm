$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_loop_inv_3_preserved_goal4:
  the strpbrk loop-invariant preservation condition concludes that the bytes
  at addresses a_5 and a_4 differ, under the null byte at a, nonzero byte at
  a_1, equal search results, memory, address-order, valid-string,
  character-range, in-array transfer, and four quantified no-match
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint64, NTP4VCValidStr, and NTP4VCInArray directly expand the
  corresponding source definitions.

  The arbitrary relations L and M represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map I and
  sets J and K represent region, linked, and sconst. N and P represent
  l_strlen and to_uint64, with their source fixed-point, range, and identity
  laws retained explicitly. Under the corrected source specification,
  l_strpbrk depends on character memory; O is that function specialized to
  this theorem's fixed memory A. Only the equality assumption stated by this
  verification condition is imposed on the specialization, and no
  cross-memory law is assumed.

  Both source let-bindings are expanded at every use. All addresses,
  integers, maps, relations, and predicates retain their unrestricted source
  domains. The witnesses in valid-string and in-array predicates remain
  internally existential, and all four no-match assumptions retain their
  full address quantifiers, quantifier order, and implication scopes.
  Splitting the source implication chain into scoped essential hypotheses is
  bidirectionally equivalent to the original statement. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr NTP4VCInArray
  NTP4VCStrlen NTP4VCStrpbrk
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strpbrk-class $a class ( NTP4VCStrpbrk A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-in-array-syntax $a wff ( NTP4VCInArray A B C D E F ) $.

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
ntp4vc-strpbrk-def $a |- ( NTP4VCStrpbrk A B C ) =
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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
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
  $d x A B C D E F $.
  ntp4vc-in-array-def $a |- (
    ( NTP4VCInArray A B C D E F )
    <->
    E. x e. NTP4VCAddr
      (
        ( A ` x ) = C
        /\
        (
          ( NTP4VCAddrLe D B x )
          /\
          (
            NTP4VCAddrLt
              E
              x
              ( NTP4VCShift B ( NTP4VCStrlen F A B ) )
          )
        )
      )
  ) $.
$}

${
  $d x y A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_1, B=a_1, C=a_2, D=a, E=a_3, F=t, G=a_4, and H=a_5.
     I is region; J and K are the linked and sconst extensions; L and M are
     the addr_le and addr_lt extensions; N and O are l_strlen and l_strpbrk;
     and P is to_uint64. Source lets are expanded as
       x=A(B) and a_6=shift(C,l_strlen(A,C)). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- E e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-a4-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a5-address $e |- H e. NTP4VCAddr $.

  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- K C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- L C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- M C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- N e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strpbrk-function $e |- O e.
    ( NTP4VCAddr ^m ( NTP4VCAddr X. NTP4VCAddr ) ) $.
  ntp4vc-to-uint64-function $e |- P e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe L x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt M x y )
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
          ( NTP4VCStrlen N x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( P ` ( 1 + ( NTP4VCStrlen N x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen N x y ) ) $.

  ntp4vc-a-null $e |- ( A ` D ) = 0 $.
  ntp4vc-a1-byte-nonzero $e |- ( A ` B ) =/= 0 $.

  ntp4vc-strpbrk-results-equal $e |- (
    ( NTP4VCStrpbrk O E C )
    =
    ( NTP4VCStrpbrk O B C )
  ) $.

  ntp4vc-region-a2 $e |- ( I ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( I ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- F e. J $.
  ntp4vc-sconst-memory $e |- A e. K $.

  ntp4vc-a2-le-a $e |- ( NTP4VCAddrLe L C D ) $.
  ntp4vc-a2-le-a4 $e |- ( NTP4VCAddrLe L C G ) $.
  ntp4vc-a3-le-a1 $e |- ( NTP4VCAddrLe L E B ) $.
  ntp4vc-a3-le-a5 $e |- ( NTP4VCAddrLe L E H ) $.

  ntp4vc-a1-byte-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr F A D ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr F A B ) $.
  ntp4vc-a2-valid-string $e |- ( NTP4VCValidStr F A C ) $.
  ntp4vc-a3-valid-string $e |- ( NTP4VCValidStr F A E ) $.

  ntp4vc-a5-before-a1-next $e |- (
    NTP4VCAddrLt M H ( NTP4VCShift B 1 )
  ) $.

  ntp4vc-a4-before-a2-end $e |- (
    NTP4VCAddrLt
      M
      G
      ( NTP4VCShift C ( NTP4VCStrlen N A C ) )
  ) $.

  ntp4vc-a-le-a2-end $e |- (
    NTP4VCAddrLe
      L
      D
      ( NTP4VCShift C ( NTP4VCStrlen N A C ) )
  ) $.

  ntp4vc-a1-le-a3-end $e |- (
    NTP4VCAddrLe
      L
      B
      ( NTP4VCShift E ( NTP4VCStrlen N A E ) )
  ) $.

  ntp4vc-in-array-transfer $e |- (
    ( NTP4VCInArray A C ( A ` B ) L M N )
    ->
    ( NTP4VCInArray A D ( A ` B ) L M N )
  ) $.

  ntp4vc-no-a2-to-a-match $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt M x D )
      ->
      (
        ( NTP4VCAddrLe L C x )
        ->
        ( A ` B ) =/= ( A ` x )
      )
    ) $.

  ntp4vc-no-a2-array-match $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLe L C x )
      ->
      (
        (
          NTP4VCAddrLt
            M
            x
            ( NTP4VCShift C ( NTP4VCStrlen N A C ) )
        )
        ->
        ( A ` B ) =/= ( A ` x )
      )
    ) $.

  ntp4vc-cross-range-distinct-strict $e |-
    A. x e. NTP4VCAddr
      A. y e. NTP4VCAddr
        (
          ( NTP4VCAddrLt M x B )
          ->
          (
            ( NTP4VCAddrLe L C y )
            ->
            (
              ( NTP4VCAddrLe L E x )
              ->
              (
                (
                  NTP4VCAddrLt
                    M
                    y
                    ( NTP4VCShift C ( NTP4VCStrlen N A C ) )
                )
                ->
                ( A ` x ) =/= ( A ` y )
              )
            )
          )
        ) $.

  ntp4vc-cross-range-distinct-nonstrict $e |-
    A. x e. NTP4VCAddr
      A. y e. NTP4VCAddr
        (
          ( NTP4VCAddrLe L x B )
          ->
          (
            ( NTP4VCAddrLe L C y )
            ->
            (
              ( NTP4VCAddrLe L E x )
              ->
              (
                (
                  NTP4VCAddrLt
                    M
                    y
                    ( NTP4VCShift C ( NTP4VCStrlen N A C ) )
                )
                ->
                ( A ` x ) =/= ( A ` y )
              )
            )
          )
        ) $.

  ntp4vc-strpbrk-loop-inv-3-preserved-goal4 $a |- (
    ( A ` H ) =/= ( A ` G )
  ) $.
$}
