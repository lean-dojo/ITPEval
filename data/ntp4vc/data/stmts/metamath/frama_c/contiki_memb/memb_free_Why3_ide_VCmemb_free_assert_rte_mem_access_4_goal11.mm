$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_assert_rte_mem_access_4_goal11:
  the memb-free verification condition establishes one-unit read validity at
  structure offset two from the generated member index, pointer identity,
  bounds, memory validity, framing, linking, constancy, member-validity, and
  no-earlier-matching-address assumptions. This file contains no proof.
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
  arrays are all retained. NTP4VCTDiv is truncating integer division toward
  zero for the positive divisor guaranteed by NTP4VCValidMemb.
  NTP4VCMembIndex and NTP4VCMembPtr directly expand l__memb_index and
  l__memb_ptr.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents the
  source linked predicate, while membership of the integer memory E in the
  arbitrary set S represents the source sconst predicate. Thus these source
  uninterpreted predicates remain arbitrary rather than receiving extra
  laws. Source let-bound terms are expanded at their uses, and the quantified
  no-earlier-matching-address condition keeps its full integer domain. The
  final declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint16 NTP4VCValidMemb
  NTP4VCTDiv NTP4VCMembIndex NTP4VCMembPtr
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-memb-index-class $a class ( NTP4VCMembIndex A B C D ) $.
ntp4vc-memb-ptr-class $a class ( NTP4VCMembPtr A B C D ) $.

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

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-memb-index-def $a |- ( NTP4VCMembIndex A B C D ) =
  (
    NTP4VCTDiv
      (
        ( NTP4VCOffset D )
        -
        ( NTP4VCOffset ( A ` ( NTP4VCShift C 3 ) ) )
      )
      ( B ` ( NTP4VCShift C 0 ) )
  ) $.

ntp4vc-memb-ptr-def $a |- ( NTP4VCMembPtr A B C D ) =
  (
    NTP4VCShift
      ( A ` ( NTP4VCShift C 3 ) )
      ( D x. ( B ` ( NTP4VCShift C 0 ) ) )
  ) $.

${
  $d x A B C D E L R S T $.

  $( Source parameters:
     A=a_1, B=a, C=t_3, D=t_1, T=t, E=t_2,
     R=region, L=linked extension, S=sconst extension.
     The source lets are expanded as:
       x=NTP4VCMembIndex(C,D,A,B), a_2=shift(A,1),
       x_1=D(a_2), and a_3=shift(A,3). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-int-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-pointer-identity $e |- (
    (
      NTP4VCMembPtr
        C
        D
        A
        ( NTP4VCMembIndex C D A B )
    )
    =
    B
  ) $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-index-nonnegative $e |- (
    0 <_ ( NTP4VCMembIndex C D A B )
  ) $.
  ntp4vc-index-lt-count $e |- (
    ( NTP4VCMembIndex C D A B )
    <
    ( D ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-index-le-count $e |- (
    ( NTP4VCMembIndex C D A B )
    <_
    ( D ` ( NTP4VCShift A 1 ) )
  ) $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed R C ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-int-memory $e |- E e. S $.

  ntp4vc-count-uint16 $e |- (
    NTP4VCUint16 ( D ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-valid-memb $e |- ( NTP4VCValidMemb T C D A ) $.

  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 3 ) 1
  ) $.
  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-index-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCMembIndex C D A B )
  ) $.

  ntp4vc-no-earlier-matching-address $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCMembIndex C D A B )
        ->
        (
          NTP4VCShift
            ( C ` ( NTP4VCShift A 3 ) )
            ( x x. ( D ` ( NTP4VCShift A 0 ) ) )
        )
        =/=
        B
      )
    ) $.

  ntp4vc-memb-free-assert-rte-mem-access-4-goal11 $a |- (
    NTP4VCValidRD T ( NTP4VCShift A 2 ) 1
  ) $.
$}
