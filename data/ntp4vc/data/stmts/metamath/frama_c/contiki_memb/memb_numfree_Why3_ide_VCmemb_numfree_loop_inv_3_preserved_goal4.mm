$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_loop_inv_3_preserved_goal4:
  the memb-numfree loop verification condition updates the count of free
  backing-array entries after inspecting the current byte, under the generated
  index bounds, memory-model, validity, framing, linking, constancy, and C
  integer-range assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint8, NTP4VCSint32,
  NTP4VCUint16, and NTP4VCValidMemb directly expand the corresponding source
  definitions. NTP4VCValidMemb retains all eight conjuncts of p_valid_memb.

  NTP4VCOccA is the finite cardinality of exactly those integer indices in
  the source half-open interval whose shifted byte-memory value equals the
  requested value. This is the extensional function characterized by the
  source l_occ_a endpoint and iteration axioms.

  The arbitrary integer-valued map G represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents the
  source linked predicate, while membership of the byte-memory map E in the
  arbitrary set S represents the source sconst predicate. The source let
  bindings are expanded at their uses. Its proposition-valued conditional is
  rendered by the equivalent equality and inequality branches. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCMaxIndex
  NTP4VCSint8Limit NTP4VCSint32Limit NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint8 NTP4VCSint32 NTP4VCUint16 NTP4VCValidMemb NTP4VCOccA
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-occ-a-class $a class ( NTP4VCOccA A B C D E ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint8-syntax
  $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint16-syntax
  $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-memb-syntax
  $a wff ( NTP4VCValidMemb A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit =
  ; ; 1 2 8 $.
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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

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
  $d x A B C D E $.
  ntp4vc-occ-a-def $a |- ( NTP4VCOccA A B C D E ) =
    (
      #
      `
      {
        x e. ZZ
        |
        (
          D <_ x
          /\
          (
            x < E
            /\
            ( A ` ( NTP4VCShift C x ) ) = B
          )
        )
      }
    ) $.
$}

${
  $d A B C D E F G H L S T $.

  $( Source parameters:
     A=a, B=t_3, C=i_2, D=t_1, E=t_2, F=i, H=i_1, T=t,
     G=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_1=shift(A,1), x=D(a_1), a_2=shift(A,2), a_3=B(a_2),
       x_1=NTP4VCOccA(E,0,a_3,0,C), x_2=1+C,
       a_4=shift(a_3,C), and x_3=E(a_4). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- B e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- C e. ZZ $.
  ntp4vc-int-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-byte-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-i2-nonnegative $e |- 0 <_ C $.
  ntp4vc-i2-lt-count $e |- C < ( D ` ( NTP4VCShift A 1 ) ) $.
  ntp4vc-i2-le-count $e |- C <_ ( D ` ( NTP4VCShift A 1 ) ) $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-occ-a-le-i2 $e |- (
    (
      NTP4VCOccA
        E
        0
        ( B ` ( NTP4VCShift A 2 ) )
        0
        C
    )
    <_
    C
  ) $.
  ntp4vc-i2-max-index $e |- C <_ NTP4VCMaxIndex $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed G B ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-byte-memory $e |- E e. S $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-count-uint16 $e |- (
    NTP4VCUint16 ( D ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-i2-plus-one-sint32 $e |- ( NTP4VCSint32 ( 1 + C ) ) $.

  ntp4vc-valid-memb $e |- ( NTP4VCValidMemb T B D A ) $.
  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 2 ) 1
  ) $.
  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 1 ) 1
  ) $.
  ntp4vc-current-byte-sint8 $e |- (
    NTP4VCSint8
      (
        E
        `
        (
          NTP4VCShift
            ( B ` ( NTP4VCShift A 2 ) )
            C
        )
      )
  ) $.
  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD
      T
      (
        NTP4VCShift
          ( B ` ( NTP4VCShift A 2 ) )
          C
      )
      1
  ) $.
  ntp4vc-occ-a-sint32 $e |- (
    NTP4VCSint32
      (
        NTP4VCOccA
          E
          0
          ( B ` ( NTP4VCShift A 2 ) )
          0
          C
      )
  ) $.

  ntp4vc-update-case $e |- (
    (
      (
        E
        `
        (
          NTP4VCShift
            ( B ` ( NTP4VCShift A 2 ) )
            C
        )
      )
      =
      0
      ->
      (
        ( 1 + F ) = H
        /\
        (
          (
            NTP4VCOccA
              E
              0
              ( B ` ( NTP4VCShift A 2 ) )
              0
              C
          )
          =
          F
          /\
          F <_ NTP4VCMaxIndex
        )
      )
    )
    /\
    (
      (
        E
        `
        (
          NTP4VCShift
            ( B ` ( NTP4VCShift A 2 ) )
            C
        )
      )
      =/=
      0
      ->
      (
        NTP4VCOccA
          E
          0
          ( B ` ( NTP4VCShift A 2 ) )
          0
          C
      )
      =
      H
    )
  ) $.

  ntp4vc-memb-numfree-loop-inv-3-preserved-goal4 $a |- (
    NTP4VCOccA
      E
      0
      ( B ` ( NTP4VCShift A 2 ) )
      0
      ( 1 + C )
  )
  =
  H $.
$}
