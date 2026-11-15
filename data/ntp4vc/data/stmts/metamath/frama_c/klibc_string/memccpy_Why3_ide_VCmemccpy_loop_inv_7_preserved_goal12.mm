$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_7_preserved_goal12:
  the memccpy loop-invariant preservation condition states that the updated
  integer memory agrees at corresponding source and destination offsets,
  under the generated bounds, byte-range, memory-validity, separation,
  address-order, linking, constancy, and quantified prefix assumptions. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCUint32, NTP4VCSint32, and NTP4VCSint8 directly expand the
  corresponding source definitions. NTP4VCHavoc is the source havoc function
  fixed pointwise by havoc_access, and NTP4VCUpdate is full-domain functional
  update.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents
  linked, while membership of the integer memory E in the arbitrary set S
  represents sconst. The arbitrary relation U represents addr_le, with its
  source law under equal bases retained as an explicit hypothesis. Thus no
  extra laws are assigned to the imported uninterpreted symbols.

  The source occurrences to_sint8 i_3 and to_uint32 (i - 1) are displayed as
  i_3 and i - 1. The explicit signed-byte bounds imply is_sint8 i_3, while
  nonzero uint32 i implies that i - 1 is uint32; the imported source axioms
  id_sint8 and id_uint32 therefore make both replacements bidirectionally
  equivalent in this verification condition. Source let-bindings are expanded
  at every use, and both quantified memory conditions keep their full integer
  domain. The final declaration is Metamath's native unproved $a statement
  encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit NTP4VCSint8Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSeparated
  NTP4VCUint32 NTP4VCSint32 NTP4VCSint8
  NTP4VCHavoc NTP4VCUpdate
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A ) $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
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
  $d x y A B C D E F G H L R S T U $.

  $( Source parameters:
     A=a_1, B=i_1, C=i, D=t_1, E=t_2, F=a, G=i_3, H=i_2, T=t.
     R is region; L and S are the linked and sconst extensions; U is the
     addr_le extension. Source lets are expanded as:
       a_2=shift(A,0), x=B-C, a_3=havoc(D,E,a_2,x),
       a_4=shift(F,x), a_5=a_3(a_4), x_1=G,
       a_6=shift(F,0), a_7=shift(A,x), and
       a_8=update(a_3,a_7,a_5). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- B e. ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-t1-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- F e. NTP4VCAddr $.
  ntp4vc-i3-integer $e |- G e. ZZ $.
  ntp4vc-i2-integer $e |- H e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- U C_ ( NTP4VCAddr X. NTP4VCAddr ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe U x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-i-nonzero $e |- C =/= 0 $.

  ntp4vc-current-byte-not-target $e |- (
    (
      (
        NTP4VCHavoc
          D E ( NTP4VCShift A 0 ) ( B - C )
      )
      `
      ( NTP4VCShift F ( B - C ) )
    )
    =/= G
  ) $.

  ntp4vc-i1-positive $e |- 0 < B $.
  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i-le-i1 $e |- C <_ B $.
  ntp4vc-i2-nonnegative $e |- 0 <_ H $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase F ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-index-bound $e |- ( H + ( C - 1 ) ) < B $.

  ntp4vc-i3-lower-bound $e |- -u ; ; 1 2 8 <_ G $.
  ntp4vc-i3-upper-bound $e |- G <_ ; ; 1 2 7 $.

  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-t2 $e |- E e. S $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-destination-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift F 0 ) B
  ) $.

  ntp4vc-source-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift A 0 ) B
  ) $.

  ntp4vc-buffers-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift F 0 ) B
      ( NTP4VCShift A 0 ) B
  ) $.

  ntp4vc-destination-start-le-current $e |- (
    NTP4VCAddrLe U F ( NTP4VCShift F ( B - C ) )
  ) $.

  ntp4vc-source-start-le-current $e |- (
    NTP4VCAddrLe U A ( NTP4VCShift A ( B - C ) )
  ) $.

  ntp4vc-destination-current-le-end $e |- (
    NTP4VCAddrLe
      U
      ( NTP4VCShift F ( B - C ) )
      ( NTP4VCShift F B )
  ) $.

  ntp4vc-source-current-le-end $e |- (
    NTP4VCAddrLe
      U
      ( NTP4VCShift A ( B - C ) )
      ( NTP4VCShift A B )
  ) $.

  ntp4vc-current-byte-sint8 $e |- (
    NTP4VCSint8
      (
        (
          NTP4VCHavoc
            D E ( NTP4VCShift A 0 ) ( B - C )
        )
        `
        ( NTP4VCShift F ( B - C ) )
      )
  ) $.

  ntp4vc-prefix-equal $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + C ) < B
        ->
        (
          (
            (
              NTP4VCHavoc
                D E ( NTP4VCShift A 0 ) ( B - C )
            )
            `
            ( NTP4VCShift A x )
          )
          =
          (
            (
              NTP4VCHavoc
                D E ( NTP4VCShift A 0 ) ( B - C )
            )
            `
            ( NTP4VCShift F x )
          )
        )
      )
    ) $.

  ntp4vc-prefix-no-target $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + C ) < B
        ->
        (
          (
            (
              NTP4VCHavoc
                D E ( NTP4VCShift A 0 ) ( B - C )
            )
            `
            ( NTP4VCShift A x )
          )
          =/= G
        )
      )
    ) $.

  ntp4vc-memccpy-loop-inv-7-preserved-goal12 $a |- (
    (
      NTP4VCUpdate
        (
          NTP4VCHavoc
            D E ( NTP4VCShift A 0 ) ( B - C )
        )
        ( NTP4VCShift A ( B - C ) )
        (
          (
            NTP4VCHavoc
              D E ( NTP4VCShift A 0 ) ( B - C )
          )
          `
          ( NTP4VCShift F ( B - C ) )
        )
    )
    `
    ( NTP4VCShift A H )
  )
  =
  (
    (
      NTP4VCUpdate
        (
          NTP4VCHavoc
            D E ( NTP4VCShift A 0 ) ( B - C )
        )
        ( NTP4VCShift A ( B - C ) )
        (
          (
            NTP4VCHavoc
              D E ( NTP4VCShift A 0 ) ( B - C )
          )
          `
          ( NTP4VCShift F ( B - C ) )
        )
    )
    `
    ( NTP4VCShift F H )
  ) $.
$}
