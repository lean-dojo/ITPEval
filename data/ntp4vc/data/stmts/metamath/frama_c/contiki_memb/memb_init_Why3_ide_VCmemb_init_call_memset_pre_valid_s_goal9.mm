$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_goal9:
  the memb-initialization verification condition establishes validity or
  emptiness for the first backing array before a memset call, under the
  generated uint16 and memory-model assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCUint16, NTP4VCValidMemb,
  NTP4VCEmptyBlock, and NTP4VCValidOrEmpty expand the corresponding source
  definitions.

  In NTP4VCEmptyBlock, the source condition
  base_offset (offset s) = 0 is represented as offset s = 0. These are
  bidirectionally equivalent from the source axioms base_offset_zero and
  base_offset_inj (whose specialization at zero also gives base_index 0 = 0).

  The arbitrary integer-valued map G represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents the
  source linked predicate, while membership of the integer memory D in the
  arbitrary set S represents the source sconst predicate. Thus the source's
  uninterpreted predicates remain arbitrary. Source let-bindings are expanded
  at every use. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCUint16 NTP4VCValidMemb NTP4VCEmptyBlock
  NTP4VCValidOrEmpty
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-uint16-syntax
  $a wff ( NTP4VCUint16 A ) $.
ntp4vc-valid-memb-syntax
  $a wff ( NTP4VCValidMemb A B C D ) $.
ntp4vc-empty-block-syntax
  $a wff ( NTP4VCEmptyBlock A B ) $.
ntp4vc-valid-or-empty-syntax
  $a wff ( NTP4VCValidOrEmpty A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
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
  $d i A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. i e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` i ) ) ) <_ 0 )
  ) $.
$}

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

ntp4vc-empty-block-def $a |- (
  ( NTP4VCEmptyBlock A B )
  <->
  (
    ( A ` ( NTP4VCBase B ) ) = 0
    /\
    ( NTP4VCOffset B ) = 0
  )
) $.

ntp4vc-valid-or-empty-def $a |- (
  ( NTP4VCValidOrEmpty A B C )
  <->
  (
    ( NTP4VCValidRW A ( NTP4VCShift B 0 ) C )
    /\
    (
      ( NTP4VCEmptyBlock A B )
      \/
      ( NTP4VCValidRD A B 1 )
    )
  )
) $.

${
  $d A B C D G L S T $.

  $( Source parameters:
     A=a, B=t_1, C=t_3, T=t, D=t_2,
     G=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_1=shift(A,1), x=B(a_1), a_2=shift(A,2). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-int-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-a $e |- (
    ( G ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed G C ) $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-int-memory $e |- D e. S $.

  ntp4vc-count-uint16 $e |- (
    NTP4VCUint16 ( B ` ( NTP4VCShift A 1 ) )
  ) $.

  ntp4vc-element-size-uint16 $e |- (
    NTP4VCUint16 ( B ` ( NTP4VCShift A 0 ) )
  ) $.

  ntp4vc-valid-memb $e |- (
    NTP4VCValidMemb T C B A
  ) $.

  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 2 ) 1
  ) $.

  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-memb-init-call-memset-pre-valid-s-goal9
    $a |- (
      NTP4VCValidOrEmpty
        T
        ( C ` ( NTP4VCShift A 2 ) )
        ( B ` ( NTP4VCShift A 1 ) )
    ) $.
$}
