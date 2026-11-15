$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_call_memset_pre_valid_s_2_goal10:
  the memb-initialization verification condition establishes validity or
  emptiness for the second backing array after a memset-style initialization,
  under the generated integer bounds and memory-model assumptions. This file
  contains no proof.
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

  NTP4VCHavoc is the source havoc function fixed pointwise by havoc_access.
  The source hypothesis l_memset (...) a_5 0 x = true is represented by its
  full-domain integer quantification. This is exactly the bidirectional
  equivalence supplied by Q_memset_def, with c = 0 and n = x.

  The source conclusion applies to_uint32 to x_2. The two uint16 premises make
  x_2 nonnegative, and the explicit signed-32 upper bound places it below
  2^32. Hence source axiom id_uint32 makes to_uint32 x_2 = x_2, so displaying
  x_2 in the conclusion is logically equivalent in this verification
  condition.

  The arbitrary integer-valued map G represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents the
  source linked predicate, while membership of the integer memory D in the
  arbitrary set S represents the source sconst predicate. Thus imported
  uninterpreted predicates remain arbitrary. Source let-bindings are expanded
  at every use. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint16Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCUint16 NTP4VCValidMemb NTP4VCEmptyBlock
  NTP4VCValidOrEmpty NTP4VCHavoc
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
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
  $d i A B C D $.
  ntp4vc-havoc-def $a |- ( NTP4VCHavoc A B C D ) =
    (
      i e. NTP4VCAddr |->
        if
        (
          ( NTP4VCSeparated i 1 C D ) ,
          ( B ` i ) ,
          ( A ` i )
        )
    ) $.
$}

${
  $d i A B C D E G L S T $.

  $( Source parameters:
     A=a, B=t_1, C=t_4, T=t, D=t_3, E=t_2,
     G=region, L=linked extension, S=sconst extension.
     Source lets are expanded as:
       a_1=shift(A,1), x=B(a_1), a_2=shift(A,0), x_1=B(a_2),
       x_2=x*x_1, a_3=shift(A,2), a_4=shift(A,3),
       and a_5=C(a_3). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-int-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-byte-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-a $e |- (
    ( G ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-product-lower-bound $e |- (
    -u NTP4VCSint32Limit
    <_
    (
      ( B ` ( NTP4VCShift A 1 ) )
      x.
      ( B ` ( NTP4VCShift A 0 ) )
    )
  ) $.

  ntp4vc-product-upper-bound $e |- (
    (
      ( B ` ( NTP4VCShift A 1 ) )
      x.
      ( B ` ( NTP4VCShift A 0 ) )
    )
    <_
    NTP4VCMaxSint32
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

  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 2 ) 1
  ) $.

  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 3 ) 1
  ) $.

  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 1 ) 1
  ) $.

  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD T ( NTP4VCShift A 0 ) 1
  ) $.

  ntp4vc-first-array-valid-or-empty $e |- (
    NTP4VCValidOrEmpty
      T
      ( C ` ( NTP4VCShift A 2 ) )
      ( B ` ( NTP4VCShift A 1 ) )
  ) $.

  ntp4vc-memset-zero $e |- A. i e. ZZ
    (
      (
        (
          0 <_ i
          /\
          i < ( B ` ( NTP4VCShift A 1 ) )
        )
        ->
        (
          (
            (
              NTP4VCHavoc
                E D
                (
                  NTP4VCShift
                    ( C ` ( NTP4VCShift A 2 ) )
                    0
                )
                ( B ` ( NTP4VCShift A 1 ) )
            )
            `
            (
              NTP4VCShift
                ( C ` ( NTP4VCShift A 2 ) )
                i
            )
          )
          =
          0
        )
      )
    ) $.

  ntp4vc-memb-init-call-memset-pre-valid-s-2-goal10
    $a |- (
      NTP4VCValidOrEmpty
        T
        ( C ` ( NTP4VCShift A 3 ) )
        (
          ( B ` ( NTP4VCShift A 1 ) )
          x.
          ( B ` ( NTP4VCShift A 0 ) )
        )
    ) $.
$}
