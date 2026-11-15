$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_3_goal17:
  the memb-allocation verification condition states that changing the first
  free byte-map entry to one decreases the counted free entries by exactly
  one, under the generated bounds, memory-validity, framing, linking,
  constancy, post-state, and no-earlier-free-entry assumptions. This file
  contains no proof.
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
  NTP4VCNumfree is the finite cardinality of exactly those integer indices in
  the source half-open range whose shifted byte-memory value is zero; this is
  the extensional occurrence-count meaning of l__memb_numfree.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map H in the arbitrary set L represents the
  source linked predicate, while membership of the byte-memory map E in the
  arbitrary set S represents the source sconst predicate. Thus these imported
  uninterpreted predicates remain arbitrary rather than being assigned extra
  laws. Source let-bound terms are expanded at their uses, the conditional
  post-state retains both branches, and the quantified prefix condition keeps
  its full integer domain. The final declaration is Metamath's native
  unproved $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint16 NTP4VCValidMemb
  NTP4VCUpdate NTP4VCNumfree
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-numfree-class $a class ( NTP4VCNumfree A B C D ) $.

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
          (
            NTP4VCValidRW
              A
              ( B ` ( NTP4VCShift D 2 ) )
              1
          )
          /\
          (
            (
              NTP4VCValidRW
                A
                ( B ` ( NTP4VCShift D 3 ) )
                1
            )
            /\
            (
              (
                NTP4VCValidRW
                  A
                  (
                    NTP4VCShift
                      ( B ` ( NTP4VCShift D 2 ) )
                      0
                  )
                  ( C ` ( NTP4VCShift D 1 ) )
              )
              /\
              (
                (
                  NTP4VCValidRW
                    A
                    (
                      NTP4VCShift
                        ( B ` ( NTP4VCShift D 3 ) )
                        0
                    )
                    (
                      ( C ` ( NTP4VCShift D 1 ) )
                      x.
                      ( C ` ( NTP4VCShift D 0 ) )
                    )
                )
                /\
                (
                  NTP4VCSeparated
                    (
                      NTP4VCShift
                        ( B ` ( NTP4VCShift D 2 ) )
                        0
                    )
                    ( C ` ( NTP4VCShift D 1 ) )
                    (
                      NTP4VCShift
                        ( B ` ( NTP4VCShift D 3 ) )
                        0
                    )
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
  $d x A B C D $.
  ntp4vc-numfree-def $a |- ( NTP4VCNumfree A B C D ) =
    (
      #
      `
      {
        x e. ZZ
        |
        (
          0 <_ x
          /\
          (
            x < ( C ` ( NTP4VCShift D 1 ) )
            /\
            (
              A
              `
              (
                NTP4VCShift
                  ( B ` ( NTP4VCShift D 2 ) )
                  x
              )
            )
            =
            0
          )
        )
      }
    ) $.
$}

${
  $d x A B C D E F G H I L R S $.

  $( Source parameters:
     A=a, B=t_4, C=t_1, D=i_2, E=t_2, F=i, G=i_1, H=t, I=t_3,
     R=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_1=shift(A,2), a_2=B(a_1), a_3=shift(A,1),
       x=C(a_3), a_4=shift(A,0), x_1=C(a_4),
       a_5=shift(a_2,D), and x_2=D*x_1. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- B e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-int-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-byte-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-updated-byte-memory $e |- I e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-current-slot-free $e |- (
    (
      E
      `
      (
        NTP4VCShift
          ( B ` ( NTP4VCShift A 2 ) )
          F
      )
    )
    =
    0
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-nonnegative $e |- 0 <_ G $.
  ntp4vc-i-lt-count $e |- F < ( C ` ( NTP4VCShift A 1 ) ) $.
  ntp4vc-i1-le-count $e |- G <_ ( C ` ( NTP4VCShift A 1 ) ) $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.
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

  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-conditional-post-state $e |- (
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
            (
              NTP4VCShift
                ( B ` ( NTP4VCShift A 2 ) )
                D
            )
          )
          =
          0
          /\
          (
            (
              NTP4VCUpdate
                E
                (
                  NTP4VCShift
                    ( B ` ( NTP4VCShift A 2 ) )
                    D
                )
                1
            )
            =
            I
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
    /\
    (
      -. ( G < ( C ` ( NTP4VCShift A 1 ) ) )
      ->
      I = E
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
          (
            NTP4VCShift
              ( B ` ( NTP4VCShift A 2 ) )
              x
          )
        )
        =/=
        0
      )
    ) $.

  ntp4vc-memb-alloc-free-found-post-3-goal17 $a |- (
    1
    +
    ( NTP4VCNumfree I B C A )
  )
  =
  ( NTP4VCNumfree E B C A ) $.
$}
