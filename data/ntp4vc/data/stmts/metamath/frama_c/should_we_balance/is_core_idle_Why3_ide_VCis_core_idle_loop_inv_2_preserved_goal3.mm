$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_loop_inv_2_preserved_goal3:
  the is-core-idle verification condition preserves the loop invariant that a
  nonzero SMT-mask entry identifies an idle CPU, under the generated integer
  bounds, first-nonzero search invariants, memory validity, framing, linking,
  and quantified scheduler-mask validity and separation assumptions. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, NTP4VCUint32, and
  NTP4VCUint8 expand the corresponding source definitions.

  The arbitrary integer function M represents to_uint32, with its source
  range and identity laws retained explicitly. K represents region,
  membership of the allocation map J in the arbitrary set L represents
  linked, N represents l_size with its imported positive signed-32 bound, O
  represents l_idle_cpu, P represents l_cpu_smt_mask, and Q, R, and S
  represent l_sched_group_cpus, l_sched_group_mask, and
  l_group_balance_mask.

  Every source let-bound address and integer is expanded at its use.
  NTP4VCTailWitness is a bidirectional definition retaining the source's
  internal existential witness over all of ZZ. The source Boolean
  if-then-else premise is rendered by its classically equivalent pair of
  equality and disequality implications. Splitting the remaining curried
  implication chain into displayed hypotheses is bidirectionally equivalent
  to the source statement. Every quantified integer ranges over all of ZZ,
  and every quantified address ranges over the full address type. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCStorage
  NTP4VCMaxSint32 NTP4VCMaxIndex NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8 NTP4VCTailWitness
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
ntp4vc-storage-class $a class ( NTP4VCStorage A B ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-tail-witness-syntax
  $a wff ( NTP4VCTailWitness A B C D ) $.

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
ntp4vc-storage-def $a |- ( NTP4VCStorage A B ) =
  ( NTP4VCShift ( A ` ( NTP4VCShift B 0 ) ) 0 ) $.

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
  ntp4vc-tail-witness-def $a |- (
    ( NTP4VCTailWitness A B C D )
    <->
    E. x e. ZZ
      (
        ( A ` ( NTP4VCShift B x ) ) =/= 0
        /\
        (
          x < D
          /\
          C <_ x
        )
      )
  ) $.
$}

${
  $d x y z w v A B C D E F G H I J K L M N O P Q R S $.

  $( Source parameters:
     A=t_2, B=t_1, C=i_5, D=i_4, E=i_2, F=i_3, G=i, H=i_1,
     I=a, and J=t. K is region, L is the extension of linked, M is
     to_uint32, N is l_size, O is l_idle_cpu, P is l_cpu_smt_mask,
     Q is l_sched_group_cpus, R is l_sched_group_mask, and S is
     l_group_balance_mask.

     The outer source lets are expanded as
       a_1=shift(P(C),0), a_2=A(a_1),
       x=B(shift(a_2,D)), and x_1=M(E).
     NTP4VCStorage A V abbreviates shift(A(shift(V,0)),0). $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-integer-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i5-integer $e |- C e. ZZ $.
  ntp4vc-i4-integer $e |- D e. ZZ $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i3-integer $e |- F e. ZZ $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-a-address $e |- I e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- J e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- N e. ZZ $.
  ntp4vc-idle-cpu-function $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- P e. ( NTP4VCAddr ^m ZZ ) $.

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
            x < N
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( P ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( P ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < N
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < N
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( P ` x ) 0 ) ) y )
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
                  ( w ` ( NTP4VCShift ( P ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( P ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < N
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < N
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < N
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( P ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.

  ntp4vc-sched-group-cpus-function
    $e |- Q e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- R e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- S e. ( NTP4VCAddr ^m NTP4VCAddr ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( M ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( M ` x ) = x
    ) $.

  ntp4vc-size-properties $e |- (
    0 < N
    /\
    N <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-selected-cpu-idle $e |- ( O ` C ) =/= 0 $.

  ntp4vc-i3-slot-nonzero $e |- (
    B
    `
    (
      NTP4VCShift
        ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
        F
    )
  ) =/= 0 $.

  ntp4vc-i-nonnegative $e |- 0 <_ G $.
  ntp4vc-i-lt-size $e |- G < N $.
  ntp4vc-i3-le-i1 $e |- F <_ H $.
  ntp4vc-i2-nonnegative $e |- 0 <_ E $.
  ntp4vc-i3-nonnegative $e |- 0 <_ F $.
  ntp4vc-i5-nonnegative $e |- 0 <_ C $.
  ntp4vc-i5-lt-size $e |- C < N $.
  ntp4vc-i2-le-size $e |- E <_ N $.
  ntp4vc-converted-i4-lt-size $e |- ( M ` D ) < N $.

  ntp4vc-region-a $e |- ( K ` ( NTP4VCBase I ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed K A ) $.
  ntp4vc-linked-allocation $e |- J e. L $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-i4-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i5-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-i1-successor-sint32 $e |- (
    NTP4VCSint32 ( 1 + H )
  ) $.

  ntp4vc-smt-mask-pointer-valid-rd $e |- (
    NTP4VCValidRD J ( NTP4VCShift ( P ` C ) 0 ) 1
  ) $.

  ntp4vc-i4-slot-uint8 $e |- (
    NTP4VCUint8
      (
        B
        `
        (
          NTP4VCShift
            ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
            D
        )
      )
  ) $.

  ntp4vc-selected-storage-valid-rd $e |- (
    NTP4VCValidRD
      J
      (
        NTP4VCShift
          ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
          0
      )
      N
  ) $.

  ntp4vc-i5-i4-branch $e |- (
    (
      C = D
      ->
      (
        C = H
        /\
        C <_ NTP4VCMaxIndex
      )
    )
    /\
    (
      C =/= D
      ->
      (
        D = H
        /\
        (
          ( O ` D ) =/= 0
          /\
          (
            0 <_ D
            /\
            (
              D < N
              /\
              D <_ NTP4VCMaxIndex
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-all-tail-zero-implies-i4-is-size $e |- (
    (
      A. x e. ZZ
        (
          x < N
          ->
          (
            ( M ` E ) <_ x
            ->
            (
              B
              `
              (
                NTP4VCShift
                  ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
                  x
              )
            )
            =
            0
          )
        )
    )
    ->
    N = D
  ) $.

  ntp4vc-tail-witness-implies-i4-nonzero $e |- (
    (
      NTP4VCTailWitness
        B
        ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
        ( M ` E )
        N
    )
    ->
    (
      B
      `
      (
        NTP4VCShift
          ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
          D
      )
    )
    =/=
    0
  ) $.

  ntp4vc-tail-witness-implies-i4-lt-size $e |- (
    (
      NTP4VCTailWitness
        B
        ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
        ( M ` E )
        N
    )
    ->
    D < N
  ) $.

  ntp4vc-tail-witness-implies-i4-bounds $e |- (
    (
      NTP4VCTailWitness
        B
        ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
        ( M ` E )
        N
    )
    ->
    (
      D < N
      /\
      ( M ` E ) <_ D
    )
  ) $.

  ntp4vc-tail-witness-implies-zero-before-i4 $e |- (
    (
      NTP4VCTailWitness
        B
        ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
        ( M ` E )
        N
    )
    ->
    A. x e. ZZ
      (
        x < D
        ->
        (
          ( M ` E ) <_ x
          ->
          (
            B
            `
            (
              NTP4VCShift
                ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
                x
            )
          )
          =
          0
        )
      )
  ) $.

  ntp4vc-idle-prefix $e |- A. x e. ZZ
    (
      (
        B
        `
        (
          NTP4VCShift
            ( A ` ( NTP4VCShift ( P ` C ) 0 ) )
            x
        )
      )
      =/=
      0
      ->
      (
        0 <_ x
        ->
        (
          x < E
          ->
          ( O ` x ) =/= 0
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < N
        ->
        (
          NTP4VCValidRD J ( NTP4VCShift I x ) 1
          /\
          (
            NTP4VCValidRW
              J
              ( NTP4VCStorage A ( NTP4VCShift I x ) )
              N
          )
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD J ( Q ` x ) 1
      /\
      (
        NTP4VCValidRD J ( NTP4VCStorage A ( Q ` x ) ) N
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < N
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage A ( Q ` x ) )
                  N
                  ( NTP4VCStorage A ( NTP4VCShift I y ) )
                  N
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD J ( R ` x ) 1
      /\
      (
        NTP4VCValidRD J ( NTP4VCStorage A ( R ` x ) ) N
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < N
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage A ( R ` x ) )
                  N
                  ( NTP4VCStorage A ( NTP4VCShift I y ) )
                  N
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD J ( S ` x ) 1
      /\
      (
        NTP4VCValidRD J ( NTP4VCStorage A ( S ` x ) ) N
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < N
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage A ( S ` x ) )
                  N
                  ( NTP4VCStorage A ( NTP4VCShift I y ) )
                  N
              )
            )
          )
      )
    ) $.

  ntp4vc-cpu-smt-mask-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < N
        ->
        (
          NTP4VCValidRD J ( P ` x ) 1
          /\
          (
            NTP4VCValidRD J ( NTP4VCStorage A ( P ` x ) ) N
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < N
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage A ( P ` x ) )
                      N
                      ( NTP4VCStorage A ( NTP4VCShift I y ) )
                      N
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-is-core-idle-loop-inv-2-preserved-goal3 $a |- (
    ( O ` F ) =/= 0
  ) $.
$}
