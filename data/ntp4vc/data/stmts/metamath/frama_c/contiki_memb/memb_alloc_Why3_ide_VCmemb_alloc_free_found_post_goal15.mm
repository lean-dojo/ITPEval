$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15:
  the memb-allocation verification condition states that, under the generated
  integer bounds, memory-validity, framing, linking, constancy, conditional
  post-state, and no-earlier-free-entry assumptions, there exists an integer
  free-slot index whose updated byte is one, whose prior byte is zero, whose
  allocated address is returned, and outside which the byte maps agree. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, and NTP4VCUint16 directly
  expand the corresponding source definitions.

  NTP4VCValidMemb expands p_valid_memb without dropping any of its eight
  conjuncts: the positive element size, signed-32 product bound, structure
  and backing-array writable regions, and separation of the two backing
  arrays are all retained. NTP4VCUpdate is full-domain functional update.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map H in the arbitrary set L represents the
  source linked predicate, while membership of the byte-memory map E in the
  arbitrary set S represents the source sconst predicate. Thus these imported
  uninterpreted predicates remain arbitrary rather than being assigned extra
  laws. Source let-bound terms are expanded at their uses. The source
  proposition-valued conditional is represented by its equivalent pair of
  implications, retaining both complete branches. Both quantified conditions
  keep their full integer domains, and the existential witness remains inside
  the conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint16 NTP4VCValidMemb NTP4VCUpdate
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint16-syntax
  $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-memb-syntax
  $a wff ( NTP4VCValidMemb A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint16-limit-def $a |- NTP4VCUint16Limit =
  ; ; ; ; 6 5 5 3 6 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-valid-rd-def $a |- ( ( NTP4VCValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NTP4VCBase B ) =/= 0
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
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

${
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint16-def $a |- ( ( NTP4VCUint16 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint16Limit )
) $.

ntp4vc-valid-memb-def $a |- (
  ( NTP4VCValidMemb A B C D )
  <->
  (
    0 < ( C ` ( NTP4VCShift D 0 ) )
    /\
    (
      (
        ( C ` ( NTP4VCShift D 1 ) )
        x.
        ( C ` ( NTP4VCShift D 0 ) )
      )
      <_
      NTP4VCMaxSint32
      /\
      (
        ( NTP4VCValidRW A D 4 )
        /\
        (
          ( NTP4VCValidRW A ( B ` ( NTP4VCShift D 2 ) ) 1 )
          /\
          (
            ( NTP4VCValidRW A ( B ` ( NTP4VCShift D 3 ) ) 1 )
            /\
            (
              (
                NTP4VCValidRW
                  A
                  ( NTP4VCShift ( B ` ( NTP4VCShift D 2 ) ) 0 )
                  ( C ` ( NTP4VCShift D 1 ) )
              )
              /\
              (
                (
                  NTP4VCValidRW
                    A
                    ( NTP4VCShift ( B ` ( NTP4VCShift D 3 ) ) 0 )
                    (
                      ( C ` ( NTP4VCShift D 1 ) )
                      x.
                      ( C ` ( NTP4VCShift D 0 ) )
                    )
                )
                /\
                (
                  NTP4VCSeparated
                    ( NTP4VCShift ( B ` ( NTP4VCShift D 2 ) ) 0 )
                    ( C ` ( NTP4VCShift D 1 ) )
                    ( NTP4VCShift ( B ` ( NTP4VCShift D 3 ) ) 0 )
                    (
                      ( C ` ( NTP4VCShift D 1 ) )
                      x.
                      ( C ` ( NTP4VCShift D 0 ) )
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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

${
  $d x y A B C D E F G H I J L R S $.

  $( Source parameters:
     A=a_1, B=t_4, C=t_1, D=i_2, E=t_3, F=i, G=i_1, H=t,
     I=t_2, J=a, R=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_2=shift(A,2), a_3=B(a_2), a_4=shift(A,1),
       x=C(a_4), a_5=shift(A,0), x_1=C(a_5),
       a_6=shift(a_3,D), a_7=shift(A,3), a_8=B(a_7),
       and x_2=D*x_1. $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- B e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-int-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-byte-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-updated-byte-memory $e |- I e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-result-address $e |- J e. NTP4VCAddr $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-current-slot-free $e |- (
    (
      E
      `
      ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) F )
    )
    =
    0
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-nonnegative $e |- 0 <_ G $.
  ntp4vc-i-lt-count $e |- F < ( C ` ( NTP4VCShift A 1 ) ) $.
  ntp4vc-i1-le-count $e |- G <_ ( C ` ( NTP4VCShift A 1 ) ) $.

  ntp4vc-region-a1 $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed R B ) $.
  ntp4vc-linked-allocation $e |- H e. L $.
  ntp4vc-sconst-byte-memory $e |- E e. S $.

  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 G ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-count-uint16 $e |- (
    NTP4VCUint16 ( C ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-element-size-uint16 $e |- (
    NTP4VCUint16 ( C ` ( NTP4VCShift A 0 ) )
  ) $.

  ntp4vc-valid-memb $e |- ( NTP4VCValidMemb H B C A ) $.
  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-conditional-post-state $e |- (
    (
      (
        G < ( C ` ( NTP4VCShift A 1 ) )
        ->
        (
          D = G
          /\
          (
            (
              E
              `
              ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) D )
            )
            =
            0
            /\
            (
              (
                NTP4VCUpdate
                  E
                  ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) D )
                  1
              )
              =
              I
              /\
              (
                (
                  NTP4VCShift
                    ( B ` ( NTP4VCShift A 3 ) )
                    ( D x. ( C ` ( NTP4VCShift A 0 ) ) )
                )
                =
                J
                /\
                (
                  -u NTP4VCSint32Limit
                  <_
                  ( D x. ( C ` ( NTP4VCShift A 0 ) ) )
                  /\
                  (
                    ( D x. ( C ` ( NTP4VCShift A 0 ) ) )
                    <_
                    NTP4VCMaxSint32
                    /\
                    (
                      ( NTP4VCValidRD H ( NTP4VCShift A 2 ) 1 )
                      /\
                      (
                        ( NTP4VCValidRD H ( NTP4VCShift A 3 ) 1 )
                        /\
                        (
                          ( NTP4VCValidRD H ( NTP4VCShift A 0 ) 1 )
                          /\
                          (
                            (
                              NTP4VCValidRD
                                H
                                (
                                  NTP4VCShift
                                    ( B ` ( NTP4VCShift A 2 ) )
                                    D
                                )
                                1
                            )
                            /\
                            (
                              NTP4VCValidRW
                                H
                                (
                                  NTP4VCShift
                                    ( B ` ( NTP4VCShift A 2 ) )
                                    D
                                )
                                1
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
        )
      )
      /\
      (
        -. ( G < ( C ` ( NTP4VCShift A 1 ) ) )
        ->
        (
          E = I
          /\
          <. 0 , 0 >. = J
        )
      )
    )
  ) $.

  ntp4vc-no-earlier-free-entry $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < G
        ->
        (
          E
          `
          ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) x )
        )
        =/=
        0
      )
    ) $.

  ntp4vc-memb-alloc-free-found-post-goal15 $a |- E. x e. ZZ
    (
      (
        I
        `
        ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) x )
      )
      =
      1
      /\
      (
        (
          E
          `
          ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) x )
        )
        =
        0
        /\
        (
          (
            NTP4VCShift
              ( B ` ( NTP4VCShift A 3 ) )
              ( x x. ( C ` ( NTP4VCShift A 0 ) ) )
          )
          =
          J
          /\
          (
            0 <_ x
            /\
            (
              x < ( C ` ( NTP4VCShift A 1 ) )
              /\
              A. y e. ZZ
                (
                  (
                    ( 0 <_ y /\ y < x )
                    \/
                    (
                      x < y
                      /\
                      y < ( C ` ( NTP4VCShift A 1 ) )
                    )
                  )
                  ->
                  (
                    E
                    `
                    ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) y )
                  )
                  =
                  (
                    I
                    `
                    ( NTP4VCShift ( B ` ( NTP4VCShift A 2 ) ) y )
                  )
                )
            )
          )
        )
      )
    ) $.
$}
