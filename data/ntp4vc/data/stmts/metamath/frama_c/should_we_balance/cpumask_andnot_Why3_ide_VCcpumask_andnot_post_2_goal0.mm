$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/cpumask_andnot_Why3_ide_VCcpumask_andnot_post_2_goal0:
  the cpumask-and-not verification condition propagates the idle-core property
  from the havoc-updated destination mask to the new memory, under the
  generated integer, conversion, memory-validity, framing, linking,
  separation, and quantified mask-update assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, and NTP4VCUint32 expand the
  corresponding source definitions. NTP4VCHavoc is the source havoc function
  fixed pointwise by havoc_access. NTP4VCIdleCore expands p_idle_core with its
  internal index universally quantified over all of ZZ.

  The arbitrary integer-valued map J represents region. Membership of the
  allocation map I in the arbitrary set K represents linked. The arbitrary
  integer function L represents to_uint32; its source range and identity laws
  are retained explicitly. M represents l_size, including its imported
  positive signed-32 bound, N represents l_cpu_smt_mask, and O represents
  l_idle_cpu.

  Every source let-bound address and memory is expanded at its use. Splitting
  the source implication chain into displayed hypotheses is bidirectionally
  equivalent to the original curried implication. All quantified indices
  still range over the full set ZZ. The final declaration is Metamath's
  native unproved $a statement encoding; this database adds no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCIdleCore
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
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
ntp4vc-idle-core-syntax
  $a wff ( NTP4VCIdleCore A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

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
  $d x A B C D E F $.
  ntp4vc-idle-core-def $a |- (
    ( NTP4VCIdleCore A B C D E F )
    <->
    A. x e. ZZ
      (
        (
          (
            B
            `
            ( NTP4VCShift
                ( A ` ( NTP4VCShift ( E ` C ) 0 ) )
                x
            )
          )
          =/=
          0
        )
        ->
        (
          0 <_ x
          ->
          (
            x < D
            ->
            ( F ` x ) =/= 0
          )
        )
      )
  ) $.
$}

${
  $d x y z w v A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=a, B=a_1, C=a_2, D=t_3, E=t_1, F=t_2, G=i, H=i_1, and I=t.
     J is region, K is the extension of linked, L is to_uint32, M is l_size,
     N is l_cpu_smt_mask, and O is l_idle_cpu.

     Source lets are expanded as:
       a_3=D(shift(A,0)), a_4=shift(a_3,0),
       a_5=D(shift(B,0)), a_6=shift(a_5,0),
       a_7=D(shift(C,0)), a_8=shift(a_7,0), and
       a_9=havoc(E,F,a_8,M). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- C e. NTP4VCAddr $.
  ntp4vc-pointer-map $e |- D e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-old-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-new-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-allocation-map $e |- I e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- M e. ZZ $.
  ntp4vc-cpu-smt-mask-function
    $e |- N e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( O ` x )
      /\
      ( O ` x ) < ; ; 2 5 6
    ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < M
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( N ` x ) 0 ) ) x )
            ) =/= 0
          )
        ) $.

  itpeval-q-mask-symm $e |- A. z e. ( ZZ ^m NTP4VCAddr )
    A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
      A. y e. ZZ
        A. x e. ZZ
          (
            (
              z `
              ( NTP4VCShift ( w ` ( NTP4VCShift ( N ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < M
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < M
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( N ` x ) 0 ) ) y )
                    ) =/= 0
                  )
                )
              )
            )
          ) $.

  itpeval-q-mask-trans $e |- A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
    A. x e. ZZ
      A. z e. ( ZZ ^m NTP4VCAddr )
        A. y e. ZZ
          A. v e. ZZ
            (
              (
                z `
                ( NTP4VCShift
                  ( w ` ( NTP4VCShift ( N ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( N ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < M
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < M
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < M
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( N ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.

  ntp4vc-idle-cpu-function $e |- O e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( L ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( L ` x ) = x
    ) $.

  ntp4vc-size-properties $e |- (
    0 < M
    /\
    M <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-a2-nonnull $e |- <. 0 , 0 >. =/= C $.
  ntp4vc-converted-i-is-size $e |- ( L ` G ) = M $.
  ntp4vc-i-nonnegative $e |- 0 <_ G $.
  ntp4vc-i1-nonnegative $e |- 0 <_ H $.
  ntp4vc-i1-lt-size $e |- H < M $.
  ntp4vc-i-le-size $e |- G <_ M $.

  ntp4vc-region-a $e |- ( J ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( J ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( J ` ( NTP4VCBase C ) ) <_ 0 $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed J D ) $.
  ntp4vc-linked-allocation $e |- I e. K $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-a-valid-rd $e |- (
    NTP4VCValidRD I A 1
  ) $.

  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD I B 1
  ) $.

  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD I C 1
  ) $.

  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD
      I
      ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) 0 )
      M
  ) $.

  ntp4vc-a6-valid-rd $e |- (
    NTP4VCValidRD
      I
      ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
      M
  ) $.

  ntp4vc-a8-valid-rw $e |- (
    NTP4VCValidRW
      I
      ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
      M
  ) $.

  ntp4vc-initial-idle-core $e |- (
    NTP4VCIdleCore
      D
      (
        NTP4VCHavoc
          E F
          ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
          M
      )
      H M N O
  ) $.

  ntp4vc-a2-a-separation-condition $e |- (
    C =/= A
    ->
    (
      NTP4VCSeparated
        ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
        M
        ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) 0 )
        M
    )
  ) $.

  ntp4vc-a2-a1-separation-condition $e |- (
    C =/= B
    ->
    (
      NTP4VCSeparated
        ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
        M
        ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) 0 )
        M
    )
  ) $.

  ntp4vc-cpu-mask-regions-separated $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < M
        ->
        (
          NTP4VCSeparated
            ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
            M
            (
              NTP4VCShift
                ( D ` ( NTP4VCShift ( N ` x ) 0 ) )
                0
            )
            M
        )
      )
    ) $.

  ntp4vc-tail-havoc-agrees-with-new-memory $e |- A. x e. ZZ
    (
      G <_ x
      ->
      (
        x < M
        ->
        (
          (
            (
              ( NTP4VCHavoc
                  E F
                  ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
                  M
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) x )
            )
            =/=
            0
          )
          <->
          (
            (
              F
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) x )
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
        x < G
        ->
        (
          (
            (
              (
                F
                `
                ( NTP4VCShift ( D ` ( NTP4VCShift A 0 ) ) x )
              )
              =
              0
            )
            /\
            (
              (
                F
                `
                ( NTP4VCShift ( D ` ( NTP4VCShift B 0 ) ) x )
              )
              =/=
              0
            )
          )
          <->
          (
            (
              ( NTP4VCHavoc
                  E F
                  ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) 0 )
                  M
              )
              `
              ( NTP4VCShift ( D ` ( NTP4VCShift C 0 ) ) x )
            )
            =/=
            0
          )
        )
      )
    ) $.

  ntp4vc-cpumask-andnot-post-2-goal0 $a |- (
    NTP4VCIdleCore D F H M N O
  ) $.
$}
