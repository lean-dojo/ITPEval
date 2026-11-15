$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_assert_rte_signed_overflow_2_goal6:
  the memb-initialization verification condition establishes that the product
  of the unsigned-16 block count and element size does not exceed the
  signed-32 maximum, under the generated memory-model, validity, and memset
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, and NTP4VCUint16 directly expand the
  corresponding source definitions.

  NTP4VCValidMemb expands p_valid_memb without dropping any of its eight
  conjuncts: the positive element size, signed-32 product bound, structure
  and backing-array writable regions, and separation of the two backing
  arrays are all retained. Its source let-bound values and addresses are
  expanded at every use.

  NTP4VCEmptyBlock is equivalent to p_empty_block: the source equations
  base_offset_zero and base_offset_inj make base_offset(offset(s)) = 0
  equivalent to offset(s) = 0. NTP4VCValidOrEmpty then directly expands
  p_valid_or_empty. NTP4VCHavoc is the source havoc function fixed pointwise
  by havoc_access. NTP4VCMemset is the full-integer-domain characterization
  of l_memset = true supplied by Q_memset_def.

  The arbitrary integer-valued map G represents the source region function.
  Membership of the allocation map D in the arbitrary set L represents the
  source linked predicate, while membership of the byte-memory map E in the
  arbitrary set S represents the source sconst predicate. Thus these imported
  uninterpreted predicates remain arbitrary rather than being assigned extra
  laws. The source implication chain is represented by the displayed
  hypotheses. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCUint16 NTP4VCValidMemb
  NTP4VCEmptyBlock NTP4VCValidOrEmpty NTP4VCHavoc NTP4VCMemset
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-uint16-limit-class $a class NTP4VCUint16Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.

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
ntp4vc-memset-syntax
  $a wff ( NTP4VCMemset A B C D ) $.

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
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
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
  $d x A B C D $.
  ntp4vc-memset-def $a |- (
    ( NTP4VCMemset A B C D )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) = C
        )
      )
  ) $.
$}

${
  $d x A B C D E F G L S $.

  $( Source parameters:
     A=a, B=t_4, C=t_1, D=t, E=t_3, F=t_2,
     G=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_1=shift(A,1), x=C(a_1), x_1=C(shift(A,0)),
       a_2=shift(A,2), and a_3=B(a_2). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- B e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-int-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- D e. ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-prior-byte-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed G B ) $.
  ntp4vc-linked-allocation $e |- D e. L $.
  ntp4vc-sconst-byte-memory $e |- E e. S $.

  ntp4vc-count-uint16 $e |- (
    NTP4VCUint16 ( C ` ( NTP4VCShift A 1 ) )
  ) $.
  ntp4vc-element-size-uint16 $e |- (
    NTP4VCUint16 ( C ` ( NTP4VCShift A 0 ) )
  ) $.

  ntp4vc-valid-memb $e |- ( NTP4VCValidMemb D B C A ) $.

  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD D ( NTP4VCShift A 2 ) 1
  ) $.
  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD D ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-a3-valid-or-empty $e |- (
    NTP4VCValidOrEmpty
      D
      ( B ` ( NTP4VCShift A 2 ) )
      ( C ` ( NTP4VCShift A 1 ) )
  ) $.

  ntp4vc-memset-zero $e |- (
    NTP4VCMemset
      (
        NTP4VCHavoc
          F
          E
          (
            NTP4VCShift
              ( B ` ( NTP4VCShift A 2 ) )
              0
          )
          ( C ` ( NTP4VCShift A 1 ) )
      )
      ( B ` ( NTP4VCShift A 2 ) )
      0
      ( C ` ( NTP4VCShift A 1 ) )
  ) $.

  ntp4vc-memb-init-assert-rte-signed-overflow-2-goal6 $a |- (
    (
      ( C ` ( NTP4VCShift A 1 ) )
      x.
      ( C ` ( NTP4VCShift A 0 ) )
    )
    <_
    NTP4VCMaxSint32
  ) $.
$}
