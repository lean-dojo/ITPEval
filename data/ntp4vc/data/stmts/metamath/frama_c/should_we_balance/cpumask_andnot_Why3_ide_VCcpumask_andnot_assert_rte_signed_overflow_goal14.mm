$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_assert_rte_signed_overflow_goal14:
  the cpumask-and-not verification condition states that the current
  nonnegative signed-32 CPU index is at most 2147483646 under the generated
  size, conversion, memory-validity, framing, linking, separation, and
  quantified mask-update assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, and NTP4VCUint8 expand the
  corresponding source definitions. NTP4VCHavoc is the source havoc function
  fixed pointwise by havoc_access.

  The arbitrary integer-valued map I represents region. Membership of the
  allocation map H in the arbitrary set J represents linked. The arbitrary
  integer function K represents to_uint32; its source range and identity laws
  are retained explicitly, and imply its source idempotence law without
  imposing a stronger wraparound definition. L represents l_size, including
  its imported positive signed-32 bound, and M represents l_cpu_smt_mask.

  Every source let-bound address, memory, and byte value is expanded at its
  use. Splitting the source implication chain into displayed hypotheses is
  bidirectionally equivalent to the original curried implication. All
  quantified indices still range over the full set ZZ. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCMaxSint32 NTP4VCMaxIndex NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
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
  $d x y z w v A B C D E F G H I J K L M N $.

  $( Source parameters:
     A=a_1, B=a_2, C=a, D=t_3, E=i, F=t_1, G=t_2, and H=t.
     I is region, J is the extension of linked, K is to_uint32,
     L is l_size, and M is l_cpu_smt_mask.

     Source lets are expanded as:
       a_3=shift(A,0), a_4=shift(B,0), a_5=shift(C,0),
       a_6=D(a_5), a_7=shift(a_6,0), a_8=D(a_3),
       a_9=shift(a_8,0), a_10=shift(a_8,E), a_11=D(a_4),
       a_12=shift(a_11,0), a_13=havoc(F,G,a_12,L),
       a_14=shift(a_6,E), a_15=a_13(a_14), and a_16=a_13(a_10). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- D e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-old-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-new-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- L e. ZZ $.
  ntp4vc-cpu-smt-mask-function
    $e |- M e. ( NTP4VCAddr ^m ZZ ) $.
  ntp4vc-idle-cpu-function $e |- N e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( K ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-size-properties $e |- (
    0 < L
    /\
    L <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( N ` x )
      /\
      ( N ` x ) < ; ; 2 5 6
    ) $.

  ntp4vc-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < L
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( M ` x ) 0 ) ) x )
            ) =/= 0
          )
        ) $.

  ntp4vc-q-mask-symm $e |- A. z e. ( ZZ ^m NTP4VCAddr )
    A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. ZZ
        A. x e. ZZ
          (
            (
              z `
              ( NTP4VCShift ( w ` ( NTP4VCShift ( M ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < L
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < L
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( M ` x ) 0 ) ) y )
                    ) =/= 0
                  )
                )
              )
            )
          ) $.

  ntp4vc-q-mask-trans
    $e |- A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. x e. ZZ
        A. z e. ( ZZ ^m NTP4VCAddr )
          A. y e. ZZ
            A. v e. ZZ
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( M ` x ) 0 ) ) y )
                ) =/= 0
                ->
                (
                  (
                    z `
                    ( NTP4VCShift
                      ( w ` ( NTP4VCShift ( M ` y ) 0 ) ) v )
                  ) =/= 0
                  ->
                  (
                    0 <_ x
                    ->
                    (
                      x < L
                      ->
                      (
                        0 <_ y
                        ->
                        (
                          y < L
                          ->
                          (
                            0 <_ v
                            ->
                            (
                              v < L
                              ->
                              (
                                z `
                                ( NTP4VCShift
                                  ( w ` ( NTP4VCShift ( M ` x ) 0 ) ) v )
                              ) =/= 0
                            )
                          )
                        )
                      )
                    )
                  )
                )
              ) $.

  ntp4vc-a2-nonnull $e |- <. 0 , 0 >. =/= B $.
  ntp4vc-converted-i-not-size $e |- ( K ` E ) =/= L $.
  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i-le-size $e |- E <_ L $.

  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( I ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( I ` ( NTP4VCBase B ) ) <_ 0 $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed I D ) $.
  ntp4vc-linked-allocation $e |- H e. J $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-a-valid-rd $e |- (
    NTP4VCValidRD H C 1
  ) $.

  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD H A 1
  ) $.

  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD H B 1
  ) $.

  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCShift A 0 ) 1
  ) $.

  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCShift B 0 ) 1
  ) $.

  ntp4vc-a7-valid-rd $e |- (
    NTP4VCValidRD
      H
      ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
      L
  ) $.

  ntp4vc-a9-valid-rd $e |- (
    NTP4VCValidRD
      H
      ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) 0 )
      L
  ) $.

  ntp4vc-a10-valid-rd $e |- (
    NTP4VCValidRD
      H
      ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) E )
      1
  ) $.

  ntp4vc-a12-valid-rw $e |- (
    NTP4VCValidRW
      H
      ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
      L
  ) $.

  ntp4vc-current-a11-slot-valid-rw $e |- (
    NTP4VCValidRW
      H
      ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) E )
      1
  ) $.

  ntp4vc-a15-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCHavoc
            F G
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
        )
        `
        ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) E )
      )
  ) $.

  ntp4vc-a16-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCHavoc
            F G
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
        )
        `
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) E )
      )
  ) $.

  ntp4vc-a2-a-separation-condition $e |- (
    B =/= C
    ->
    (
      NTP4VCSeparated
        ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
        L
        ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
        L
    )
  ) $.

  ntp4vc-a2-a1-separation-condition $e |- (
    B =/= A
    ->
    (
      NTP4VCSeparated
        ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
        L
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) 0 )
        L
    )
  ) $.

  ntp4vc-a16-boolean $e |- (
    (
      (
        ( NTP4VCHavoc
            F G
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
        )
        `
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) E )
      )
      =
      0
    )
    \/
    (
      (
        ( NTP4VCHavoc
            F G
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
        )
        `
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) E )
      )
      =
      1
    )
  ) $.

  ntp4vc-a16-zero-or-source-readable $e |- (
    (
      (
        ( NTP4VCHavoc
            F G
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
        )
        `
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) E )
      )
      =
      0
    )
    \/
    (
      ( NTP4VCValidRD H ( NTP4VCShift C 0 ) 1 )
      /\
      (
        (
          NTP4VCValidRD
            H
            ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) E )
            1
        )
        /\
        (
          (
            (
              ( NTP4VCHavoc
                  F G
                  ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
                  L
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) E )
            )
            =
            0
          )
          \/
          (
            (
              ( NTP4VCHavoc
                  F G
                  ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
                  L
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) E )
            )
            =
            1
          )
        )
      )
    )
  ) $.

  ntp4vc-cpu-mask-regions-separated $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < L
        ->
        (
          NTP4VCSeparated
            ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
            L
            (
              NTP4VCShift
                ( D ` ( NTP4VCShift ( M ` x ) 0 ) )
                0
            )
            L
        )
      )
    ) $.

  ntp4vc-tail-havoc-agrees-with-new-memory $e |- A. x e. ZZ
    (
      E <_ x
      ->
      (
        x < L
        ->
        (
          (
            (
              ( NTP4VCHavoc
                  F G
                  ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
                  L
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) x )
            )
            =/=
            0
          )
          <->
          (
            (
              G
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) x )
            )
            =/=
            0
          )
        )
      )
    ) $.

  ntp4vc-prefix-andnot-relation $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < E
        ->
        (
          (
            (
              (
                G
                `
                ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) x )
              )
              =
              0
            )
            /\
            (
              (
                G
                `
                ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) x )
              )
              =/=
              0
            )
          )
          <->
          (
            (
              ( NTP4VCHavoc
                  F G
                  ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
                  L
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) x )
            )
            =/=
            0
          )
        )
      )
    ) $.

  ntp4vc-cpumask-andnot-assert-rte-signed-overflow-goal14
    $a |- E <_ NTP4VCMaxIndex $.
$}
