$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strchrnul_Why3_ide_VCstrchrnul_loop_inv_preserved_goal2:
  the strchrnul loop-invariant preservation condition concludes that advancing
  the current address by one yields a valid string, under the generated
  exact 8- and 64-bit integer conversions, cross-projection, string-search,
  address-order, memory-validity, linking, constancy, integer-range, and
  no-earlier-match assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint8, NTP4VCSint32, NTP4VCSint64, NTP4VCUint64, and
  NTP4VCValidStr directly expand the corresponding source definitions.

  The arbitrary relations I and J represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map F and
  sets G and H represent region, linked, and sconst. K, L, O, and P represent
  to_sint8, to_uint64, to_uint8, and to_sint64, while M and N represent
  l_strlen and l_strchrnul. Their exact range, identity, cross-projection, and
  fixed-point laws are retained as explicit hypotheses without assigning
  stronger properties to these symbols.

  Both source let-bindings are expanded at every use. All addresses, integers,
  functions, relations, and predicates retain their unrestricted source
  domains. The existential null-position witnesses in all valid-string
  occurrences remain internal, and the no-earlier-match assumption retains
  its full address quantifier and implication scope. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint8Limit NTP4VCSint32Limit
  NTP4VCSint64Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint8 NTP4VCSint32 NTP4VCSint64
  NTP4VCUint64 NTP4VCValidStr
  NTP4VCStrlen NTP4VCStrchrnul
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-sint64-limit-class $a class NTP4VCSint64Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strchrnul-class $a class ( NTP4VCStrchrnul A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-sint64-syntax $a wff ( NTP4VCSint64 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
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
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strchrnul-def $a |- ( NTP4VCStrchrnul A B C D ) =
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

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
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
  $d x y z A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, D=i, and E=t.
     F is region; G and H are the linked and sconst extensions; I and J are
     the addr_le and addr_lt extensions; K, L, O, and P are to_sint8,
     to_uint64, to_uint8, and to_sint64; M and N are l_strlen and
     l_strchrnul. Source lets are expanded as x=A(B) and x_1=K(D). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- G C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- H C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- I C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- J C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-sint8-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint64-function $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint8-function $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint64-function $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- M e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strchrnul-function $e |- N e.
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
        ( NTP4VCAddrLe I x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt J x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( K ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
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

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( O ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
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
    ( ( K ` ( O ` x ) ) = ( K ` x ) ) $.

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

  ntp4vc-strchrnul-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrchrnul N x y z )
            =
            if
            (
              ( x ` y ) = z ,
              y ,
              if
              (
                ( x ` y ) = 0 ,
                y ,
                ( NTP4VCStrchrnul N x ( NTP4VCShift y 1 ) z )
              )
            )
          ) $.

  ntp4vc-current-value-nonzero $e |- ( A ` B ) =/= 0 $.

  ntp4vc-current-value-not-target $e |- (
    ( A ` B ) =/= ( K ` D )
  ) $.

  ntp4vc-strchrnul-result-equality $e |- (
    ( NTP4VCStrchrnul N A C ( K ` D ) )
    =
    ( NTP4VCStrchrnul N A B ( K ` D ) )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( F ` ( NTP4VCBase C ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. G $.
  ntp4vc-sconst-memory $e |- A e. H $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe I C B ) $.
  ntp4vc-current-value-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr E A B ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr E A C ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      I
      B
      ( NTP4VCShift C ( NTP4VCStrlen M A C ) )
  ) $.

  ntp4vc-no-earlier-match $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt J x B )
      ->
      (
        ( NTP4VCAddrLe I C x )
        ->
        ( A ` x ) =/= ( K ` D )
      )
    ) $.

  ntp4vc-strchrnul-loop-inv-preserved-goal2 $a |- (
    NTP4VCValidStr E A ( NTP4VCShift B 1 )
  ) $.
$}
