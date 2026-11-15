$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strreplace_Why3_ide_VCstrreplace_loop_inv_preserved_goal4:
  the strreplace loop-invariant preservation condition concludes that the
  conditionally updated memory is a valid string from the address following
  the current character, under the generated string-termination,
  memory-havoc, replacement-branch, address-order, linking, constancy,
  exact signed- and unsigned-64 conversion, integer-range, unchanged-suffix,
  and transformed-prefix assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCSint8, NTP4VCSint64, NTP4VCUint64, and NTP4VCValidStr directly
  expand the corresponding source definitions. NTP4VCHavoc is fixed
  pointwise by havoc_access, and NTP4VCUpdate is full-domain functional
  update.

  The arbitrary integer-valued map I represents region. Membership of the
  allocation map E in the arbitrary set J represents linked, while membership
  of the memory A in the arbitrary set K represents sconst. The arbitrary
  relations L and M represent addr_le and addr_lt, with their source laws
  under equal bases retained explicitly. N and P represent to_uint64 and
  to_sint64, while O represents l_strlen. Their exact range, identity,
  signed/unsigned cross-projection, and fixed-point laws are retained without
  assigning stronger properties to these symbols.

  The source let-bindings are expanded at every use:
    x = strlen(A,B),
    a_2 = shift(B,x),
    a_3 = havoc(C,A,shift(B,0),x), and
    a_4 = a_3(D).
  All addresses, integers, maps, relations, predicates, and quantified
  indices retain their unrestricted source domains. The existential
  null-position witnesses in all three valid-string propositions remain
  internal. The source conditional equality defining H is rendered by the
  equivalent pair of implications for a_4 = F and a_4 =/= F. Splitting the
  curried implication chain into scoped essential hypotheses is
  bidirectionally equivalent for the arbitrary displayed parameters. The
  final declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCSint64Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW NTP4VCSeparated
  NTP4VCSint8 NTP4VCSint64 NTP4VCUint64 NTP4VCValidStr
  NTP4VCHavoc NTP4VCUpdate NTP4VCStrlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint64-limit-class $a class NTP4VCSint64Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint64-syntax $a wff ( NTP4VCSint64 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
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

ntp4vc-separated-def $a |- ( ( NTP4VCSeparated A B C D ) <->
  (
    B <_ 0
    \/
    (
      D <_ 0
      \/
      (
        ( NTP4VCBase A ) =/= ( NTP4VCBase C )
        \/
        (
          ( ( NTP4VCOffset C ) + D ) <_ ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCOffset C )
        )
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
  $d x A B C D $.
  ntp4vc-havoc-def $a |- ( NTP4VCHavoc A B C D ) =
    (
      x e. NTP4VCAddr |->
        if
        (
          ( NTP4VCSeparated x 1 C D ) ,
          ( B ` x ) ,
          ( A ` x )
        )
    ) $.
$}

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
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
  $d x y z A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_2, B=a_1, C=t_1, D=a, E=t, F=i, G=i_1, and H=t_3.
     I is region; J and K are the linked and sconst extensions; L and M are
     the addr_le and addr_lt extensions; N and P are to_uint64 and to_sint64;
     and O is l_strlen. The four source let-bindings are expanded as
     described above. $)

  ntp4vc-t2-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-t3-memory $e |- H e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- K C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- L C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- M C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint64-function $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint64-function $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- O e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.

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
    ( NTP4VCUint64 ( N ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( N ` x ) = x
    ) $.

  ntp4vc-to-sint64-range $e |- A. x e. ZZ
    ( NTP4VCSint64 ( P ` x ) ) $.

  ntp4vc-to-sint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint64 x )
      ->
      ( P ` x ) = x
    ) $.

  ntp4vc-proj-int64 $e |- A. x e. ZZ
    ( ( P ` ( N ` x ) ) = ( P ` x ) ) $.

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

  ntp4vc-source-end-null $e |- (
    (
      A
      `
      ( NTP4VCShift B ( NTP4VCStrlen O A B ) )
    )
    =
    0
  ) $.

  ntp4vc-current-value-nonzero $e |- (
    (
      (
        NTP4VCHavoc
          C A
          ( NTP4VCShift B 0 )
          ( NTP4VCStrlen O A B )
      )
      `
      D
    )
    =/=
    0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( I ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- E e. J $.
  ntp4vc-sconst-t2 $e |- A e. K $.
  ntp4vc-i-sint8 $e |- ( NTP4VCSint8 F ) $.
  ntp4vc-i1-sint8 $e |- ( NTP4VCSint8 G ) $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe L B D ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr E A B ) $.

  ntp4vc-source-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrlen O A B )
  ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      L
      D
      ( NTP4VCShift B ( NTP4VCStrlen O A B ) )
  ) $.

  ntp4vc-current-value-sint8 $e |- (
    NTP4VCSint8
      (
        (
          NTP4VCHavoc
            C A
            ( NTP4VCShift B 0 )
            ( NTP4VCStrlen O A B )
        )
        `
        D
      )
  ) $.

  ntp4vc-current-valid-string $e |- (
    NTP4VCValidStr
      E
      (
        NTP4VCHavoc
          C A
          ( NTP4VCShift B 0 )
          ( NTP4VCStrlen O A B )
      )
      D
  ) $.

  ntp4vc-updated-a1-valid-string $e |- (
    NTP4VCValidStr
      E
      (
        NTP4VCHavoc
          C A
          ( NTP4VCShift B 0 )
          ( NTP4VCStrlen O A B )
      )
      B
  ) $.

  ntp4vc-replacement-branch $e |- (
    (
      (
        (
          NTP4VCHavoc
            C A
            ( NTP4VCShift B 0 )
            ( NTP4VCStrlen O A B )
        )
        `
        D
      )
      =
      F
      ->
      (
        NTP4VCUpdate
          (
            NTP4VCHavoc
              C A
              ( NTP4VCShift B 0 )
              ( NTP4VCStrlen O A B )
          )
          D
          G
      )
      =
      H
    )
    /\
    (
      (
        (
          NTP4VCHavoc
            C A
            ( NTP4VCShift B 0 )
            ( NTP4VCStrlen O A B )
        )
        `
        D
      )
      =/=
      F
      ->
      (
        NTP4VCHavoc
          C A
          ( NTP4VCShift B 0 )
          ( NTP4VCStrlen O A B )
      )
      =
      H
    )
  ) $.

  ntp4vc-no-null-before-source-end $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrlen O A B )
        ->
        ( A ` ( NTP4VCShift B x ) ) =/= 0
      )
    ) $.

  ntp4vc-unchanged-suffix $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLe L D x )
      ->
      (
        (
          NTP4VCAddrLt
            M x
            ( NTP4VCShift B ( NTP4VCStrlen O A B ) )
        )
        ->
        (
          (
            NTP4VCHavoc
              C A
              ( NTP4VCShift B 0 )
              ( NTP4VCStrlen O A B )
          )
          `
          x
        )
        =
        ( A ` x )
      )
    ) $.

  ntp4vc-replaced-prefix $e |- A. x e. NTP4VCAddr
    (
      ( A ` x ) = F
      ->
      (
        ( NTP4VCAddrLt M x D )
        ->
        (
          ( NTP4VCAddrLe L B x )
          ->
          (
            (
              NTP4VCHavoc
                C A
                ( NTP4VCShift B 0 )
                ( NTP4VCStrlen O A B )
            )
            `
            x
          )
          =
          G
        )
      )
    ) $.

  ntp4vc-unchanged-prefix $e |- A. x e. NTP4VCAddr
    (
      ( A ` x ) =/= F
      ->
      (
        ( NTP4VCAddrLt M x D )
        ->
        (
          ( NTP4VCAddrLe L B x )
          ->
          (
            (
              NTP4VCHavoc
                C A
                ( NTP4VCShift B 0 )
                ( NTP4VCStrlen O A B )
            )
            `
            x
          )
          =
          ( A ` x )
        )
      )
    ) $.

  ntp4vc-strreplace-loop-inv-preserved-goal4 $a |- (
    NTP4VCValidStr E H ( NTP4VCShift D 1 )
  ) $.
$}
