$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strncat_Why3_ide_VCstrncat_loop_inv_2_preserved_goal4:
  the strncat loop-invariant preservation condition concludes that advancing
  the current destination address by one still yields a valid string, under
  the generated bounded-string-length, null-position, memory-validity,
  address-order, linking, constancy, exact unsigned- and signed-64 conversion,
  byte-range, capacity, and no-earlier-null assumptions. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCSint64, NTP4VCUint64, NTP4VCValidStr, and NTP4VCValidStrn directly
  expand the corresponding source definitions.

  The arbitrary integer-valued map K represents region. Membership of the
  allocation map F in the arbitrary set L represents linked, while membership
  of the integer memory E in the arbitrary set M represents sconst. The
  arbitrary relation N represents addr_le, with its source law under equal
  bases retained explicitly. The arbitrary higher-order maps O and P
  represent l_strlen and l_strnlen, while Q and R represent to_uint64 and
  to_sint64. Their fixed-point, exact range and identity, and signed/unsigned
  cross-projection laws retain the relevant imported source theory without
  assigning stronger properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  maps, relations, and predicates keep their original unrestricted domains.
  The existential null-position witnesses in NTP4VCValidStr,
  NTP4VCValidStrn, and the conditional hypotheses remain internally
  quantified over all integers. Splitting the source implication chain into
  scoped essential hypotheses is bidirectionally equivalent to the original
  statement. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCSint64Limit NTP4VCUint64Limit NTP4VCMaxUint64
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSint8 NTP4VCSint64 NTP4VCUint64
  NTP4VCValidStr NTP4VCValidStrn NTP4VCStrlen NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint64-limit-class $a class NTP4VCSint64Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.
ntp4vc-max-uint64-class $a class NTP4VCMaxUint64 $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint64-syntax $a wff ( NTP4VCSint64 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-valid-strn-syntax $a wff ( NTP4VCValidStrn A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-sint64-limit-def $a |- NTP4VCSint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  9 2 2 3 3 7 2 0 3 6 8 5 4 7 7 5 8 0 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.
ntp4vc-max-uint64-def $a |- NTP4VCMaxUint64 =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 5 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strnlen-def $a |- ( NTP4VCStrnlen A B C D ) =
  ( A ` <. <. B , C >. , D >. ) $.

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
  $d x y A B C D $.
  ntp4vc-valid-strn-def $a |- ( ( NTP4VCValidStrn A B C D ) <->
    (
      ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + D ) )
      \/
      (
        E. x e. ZZ
          (
            ( B ` ( NTP4VCShift C x ) ) = 0
            /\
            (
              x < D
              /\
              (
                ( NTP4VCUint64 x )
                /\
                (
                  NTP4VCValidRW
                    A
                    ( NTP4VCShift C 0 )
                    ( 1 + x )
                )
              )
            )
          )
        /\
        A. y e. ZZ
          (
            y <_ D
            ->
            ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
          )
      )
    )
  ) $.
$}

${
  $d x y z A B C D E F K L M N O P Q R $.

  $( Source parameters:
     A=a_2, B=a, C=a_1, D=i, E=t_1, and F=t.
     K is region; L and M are the linked and sconst extensions; N is the
     addr_le extension; O is l_strlen; P is l_strnlen; Q is to_uint64; and R
     is to_sint64. Source lets are expanded as:
       x=E(A), x_1=NTP4VCStrlen(O,E,B),
       a_3=NTP4VCShift(B,NTP4VCStrlen(O,E,B)),
       x_2=NTP4VCStrnlen(P,E,C,D), and
       x_3=E(NTP4VCShift(C,NTP4VCStrnlen(P,E,C,D))). $)

  ntp4vc-a2-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- M C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- N C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- O e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-strnlen-function $e |- P e.
    (
      ZZ
      ^m
      ( ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) X. ZZ )
    ) $.
  ntp4vc-to-uint64-function $e |- Q e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint64-function $e |- R e. ( ZZ ^m ZZ ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe N x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
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

  ntp4vc-to-sint64-range $e |- A. x e. ZZ
    ( NTP4VCSint64 ( R ` x ) ) $.

  ntp4vc-to-sint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint64 x )
      ->
      ( R ` x ) = x
    ) $.

  ntp4vc-proj-int64 $e |- A. x e. ZZ
    ( ( R ` ( Q ` x ) ) = ( R ` x ) ) $.

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

  ntp4vc-strnlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrnlen P x y z )
            =
            if
            (
              (
                z = 0
                \/
                ( x ` ( NTP4VCShift y 0 ) ) = 0
              ) ,
              0 ,
              (
                Q
                `
                (
                  1
                  +
                  (
                    NTP4VCStrnlen
                      P
                      x
                      ( NTP4VCShift y 1 )
                      ( Q ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-strnlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCStrnlen P x y z ) ) $.

  ntp4vc-i-nonzero $e |- D =/= 0 $.
  ntp4vc-current-byte-nonzero $e |- ( E ` A ) =/= 0 $.

  ntp4vc-destination-end-null $e |- (
    (
      E
      `
      ( NTP4VCShift B ( NTP4VCStrlen O E B ) )
    )
    =
    0
  ) $.

  ntp4vc-region-a $e |- ( K ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( K ` ( NTP4VCBase C ) ) <_ 0 $.

  ntp4vc-combined-length-bound $e |- (
    ( D + ( NTP4VCStrlen O E B ) )
    <_
    NTP4VCMaxUint64
  ) $.

  ntp4vc-linked-allocation $e |- F e. L $.
  ntp4vc-sconst-memory $e |- E e. M $.
  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 D ) $.
  ntp4vc-a-le-a2 $e |- ( NTP4VCAddrLe N B A ) $.
  ntp4vc-current-byte-sint8 $e |- ( NTP4VCSint8 ( E ` A ) ) $.
  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr F E B ) $.
  ntp4vc-a2-valid-string $e |- ( NTP4VCValidStr F E A ) $.

  ntp4vc-a-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrlen O E B )
  ) $.

  ntp4vc-a1-valid-bounded-string $e |- (
    NTP4VCValidStrn F E C D
  ) $.

  ntp4vc-a1-bounded-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrnlen P E C D )
  ) $.

  ntp4vc-a2-le-a-end $e |- (
    NTP4VCAddrLe
      N
      A
      ( NTP4VCShift B ( NTP4VCStrlen O E B ) )
  ) $.

  ntp4vc-a1-terminal-byte-sint8 $e |- (
    NTP4VCSint8
      (
        E
        `
        ( NTP4VCShift C ( NTP4VCStrnlen P E C D ) )
      )
  ) $.

  ntp4vc-combined-region-valid $e |- (
    NTP4VCValidRW
      F
      ( NTP4VCShift B 0 )
      ( ( 1 + D ) + ( NTP4VCStrlen O E B ) )
  ) $.

  ntp4vc-no-null-through-bound-implies-full-length $e |- (
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x <_ D
          ->
          ( E ` ( NTP4VCShift C x ) ) =/= 0
        )
      )
    ->
    ( NTP4VCStrnlen P E C D ) = D
  ) $.

  ntp4vc-null-through-bound-implies-terminal-null $e |- (
    E. x e. ZZ
      (
        ( E ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          0 <_ x
          /\
          x <_ D
        )
      )
    ->
    (
      E
      `
      ( NTP4VCShift C ( NTP4VCStrnlen P E C D ) )
    )
    =
    0
  ) $.

  ntp4vc-null-through-bound-implies-no-earlier-null $e |- (
    E. x e. ZZ
      (
        ( E ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          0 <_ x
          /\
          x <_ D
        )
      )
    ->
    A. y e. ZZ
      (
        0 <_ y
        ->
        (
          y < ( NTP4VCStrnlen P E C D )
          ->
          ( E ` ( NTP4VCShift C y ) ) =/= 0
        )
      )
  ) $.

  ntp4vc-no-null-before-a-end $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrlen O E B )
        ->
        ( E ` ( NTP4VCShift B x ) ) =/= 0
      )
    ) $.

  ntp4vc-strncat-loop-inv-2-preserved-goal4 $a |- (
    NTP4VCValidStr F E ( NTP4VCShift A 1 )
  ) $.
$}
