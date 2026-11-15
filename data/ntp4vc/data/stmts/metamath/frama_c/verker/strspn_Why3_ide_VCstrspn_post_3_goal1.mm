$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strspn_Why3_ide_VCstrspn_post_3_goal1: the generated strspn
  postcondition concludes that the byte at a designated input-string address
  occurs between the accept-string start and its computed end, under the
  source offset, string-span, address-order, memory-validity, linking,
  constancy, integer-range, conditional branch, no-match, and cross-range
  witness assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint64, NTP4VCValidStr, and NTP4VCInArray directly expand the
  corresponding source definitions.

  The arbitrary relations M and N represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map J and
  sets K and L represent region, linked, and sconst. O, P, and Q represent
  l_strlen, l_strspn, and to_uint64; their source fixed-point, range,
  identity, base-case, in-accept, and not-in-accept laws are retained as
  explicit hypotheses without assigning stronger properties to these
  symbols.

  All six source let-bindings are expanded at every use. The equality-bound
  branch variables i_1 and i_2 are eliminated by substituting their required
  common value i; universal implication with either equality premise is
  bidirectionally equivalent to the substituted branch. The
  proposition-valued conditional premise is rendered by the classically
  equivalent conjunction of its zero-branch and nonzero-branch implications.
  All addresses, integers, maps, relations, and predicates retain their
  unrestricted source domains. The witnesses in valid-string and in-array
  predicates remain internally existential. The no-match and cross-range
  assumptions retain their full address quantifiers, quantifier order,
  implication scopes, and internal existential witness. Splitting the source
  implication chain into scoped essential hypotheses is bidirectionally
  equivalent to the original statement. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr NTP4VCInArray
  NTP4VCStrlen NTP4VCStrspn
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strspn-class $a class ( NTP4VCStrspn A B C ) $.

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
ntp4vc-strspn-def $a |- ( NTP4VCStrspn A B C ) =
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
  $d x y z A B C D E F G H I J K L M N O P Q $.

  $( Source parameters:
     A=t_1, B=a_1, C=a, D=a_2, E=a_3, F=i, G=t, H=a_5, and I=a_4.
     J is region; K and L are the linked and sconst extensions; M and N are
     the addr_le and addr_lt extensions; O and P are l_strlen and l_strspn;
     and Q is to_uint64. Source lets are expanded as
       x=offset(B), x_1=offset(C), x_2=l_strlen(A,C), x_3=A(B),
       x_4=A(D), and a_6=shift(E,l_strlen(A,E)). The equality-bound source
       variables i_1 and i_2 are both substituted by F=i. $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- E e. NTP4VCAddr $.
  ntp4vc-index $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-a5-address $e |- H e. NTP4VCAddr $.
  ntp4vc-a4-address $e |- I e. NTP4VCAddr $.

  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- L C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- M C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- N C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- O e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strspn-function $e |- P e.
    ( ZZ ^m ( NTP4VCAddr X. NTP4VCAddr ) ) $.
  ntp4vc-to-uint64-function $e |- Q e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe M x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt N x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( Q ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( Q ` x ) = x
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
            ( Q ` ( 1 + ( NTP4VCStrlen O x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen O x y ) ) $.

  ntp4vc-strspn-base-case $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. NTP4VCAddr
          (
            ( x ` y ) = 0
            ->
            ( NTP4VCStrspn P y z ) = 0
          ) $.

  ntp4vc-strspn-not-in-accept $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. NTP4VCAddr
          (
            ( x ` y ) =/= 0
            ->
            (
              -. ( NTP4VCInArray x z ( x ` y ) M N O )
              ->
              ( NTP4VCStrspn P y z ) = 0
            )
          ) $.

  ntp4vc-strspn-in-accept $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. NTP4VCAddr
          (
            ( x ` y ) =/= 0
            ->
            (
              ( NTP4VCInArray x z ( x ` y ) M N O )
              ->
              (
                1
                +
                ( NTP4VCStrspn P ( NTP4VCShift y 1 ) z )
              )
              =
              ( NTP4VCStrspn P y z )
            )
          ) $.

  ntp4vc-offset-strspn-equality $e |- (
    (
      ( NTP4VCOffset B )
      +
      ( NTP4VCStrspn P B E )
    )
    =
    (
      ( NTP4VCOffset C )
      +
      ( NTP4VCStrspn P C E )
    )
  ) $.

  ntp4vc-a-offset-le-a1-offset $e |- (
    ( NTP4VCOffset C ) <_ ( NTP4VCOffset B )
  ) $.

  ntp4vc-region-a $e |- ( J ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( J ` ( NTP4VCBase E ) ) <_ 0 $.

  ntp4vc-a1-offset-le-a-end-offset $e |- (
    ( NTP4VCOffset B )
    <_
    (
      ( NTP4VCOffset C )
      +
      ( NTP4VCStrlen O A C )
    )
  ) $.

  ntp4vc-linked-allocation $e |- G e. K $.
  ntp4vc-sconst-memory $e |- A e. L $.
  ntp4vc-index-uint64 $e |- ( NTP4VCUint64 F ) $.

  ntp4vc-a-le-a1 $e |- ( NTP4VCAddrLe M C B ) $.
  ntp4vc-a-le-a5 $e |- ( NTP4VCAddrLe M C H ) $.

  ntp4vc-a1-byte-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a2-byte-sint8 $e |- ( NTP4VCSint8 ( A ` D ) ) $.

  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr G A C ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr G A B ) $.
  ntp4vc-a3-valid-string $e |- ( NTP4VCValidStr G A E ) $.

  ntp4vc-offset-difference-uint64 $e |- (
    NTP4VCUint64 ( ( NTP4VCOffset B ) - ( NTP4VCOffset C ) )
  ) $.

  ntp4vc-a5-before-shift-a-i $e |- (
    NTP4VCAddrLt
      N
      H
      ( NTP4VCShift C F )
  ) $.

  ntp4vc-a1-le-a-end $e |- (
    NTP4VCAddrLe
      M
      B
      ( NTP4VCShift C ( NTP4VCStrlen O A C ) )
  ) $.

  ntp4vc-conditional-state $e |- (
    (
      ( A ` B ) = 0
      ->
      ( F + ( NTP4VCOffset C ) ) = ( NTP4VCOffset B )
    )
    /\
    (
      ( A ` B ) =/= 0
      ->
      (
        D = B
        /\
        (
          ( A ` I ) = 0
          /\
          (
            ( F + ( NTP4VCOffset C ) ) = ( NTP4VCOffset D )
            /\
            (
              ( NTP4VCAddrLe M E I )
              /\
              (
                ( NTP4VCValidStr G A I )
                /\
                (
                  -. ( NTP4VCInArray A E ( A ` D ) M N O )
                  /\
                  (
                    ( NTP4VCAddrLe
                        M I
                        ( NTP4VCShift E ( NTP4VCStrlen O A E ) ) )
                    /\
                    A. x e. NTP4VCAddr
                      (
                        ( NTP4VCAddrLt N x I )
                        ->
                        (
                          ( NTP4VCAddrLe M E x )
                          ->
                          ( A ` D ) =/= ( A ` x )
                        )
                      )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a-to-a1-cross-range-witness $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt N x B )
      ->
      (
        ( NTP4VCAddrLe M C x )
        ->
        E. y e. NTP4VCAddr
          (
            ( A ` x ) = ( A ` y )
            /\
            (
              ( NTP4VCAddrLe M E y )
              /\
              (
                NTP4VCAddrLt
                  N
                  y
                  ( NTP4VCShift E ( NTP4VCStrlen O A E ) )
              )
            )
          )
      )
    ) $.

  ntp4vc-strspn-post-3-goal1 $a |- (
    NTP4VCInArray A E ( A ` H ) M N O
  ) $.
$}
