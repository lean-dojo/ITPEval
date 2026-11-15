$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/is_core_idle_Why3_ide_VCis_core_idle_call_find_next_bit_pre_2_goal8:
  the is-core-idle verification condition establishes read validity for the
  SMT-mask storage reached from the selected CPU, under the generated integer
  bounds, memory validity, framing, linking, idle-CPU, and quantified
  scheduler-mask validity and separation assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, and NTP4VCUint32 expand the
  corresponding source definitions.

  The arbitrary integer-valued map H represents region. Membership of the
  allocation map F in the arbitrary set I represents linked. J represents
  l_size, including its imported positive signed-32 bound; K represents
  l_idle_cpu; L represents l_cpu_smt_mask; and M, N, and O represent
  l_sched_group_cpus, l_sched_group_mask, and l_group_balance_mask.

  The source lets a_1 and a_2 and every let inside a quantified assumption are
  expanded at their uses. Splitting the source implication chain into
  displayed hypotheses is bidirectionally equivalent to the original curried
  implication. Every quantified integer still ranges over all of ZZ, and
  every quantified address ranges over the full address type. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-framed-syntax $a wff ( NTP4VCFramed A B ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.

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
  $d x y z w v A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=t_2, B=i_2, C=i, D=i_1, E=a, F=t, and G=t_1.
     H is region, I is the extension of linked, J is l_size, K is
     l_idle_cpu, L is l_cpu_smt_mask, M is l_sched_group_cpus, N is
     l_sched_group_mask, and O is l_group_balance_mask.

     The outer source lets are expanded as
       a_1=shift(L(B),0) and a_2=A(a_1).
     In the separation assumptions, the destination CPU-mask storage for an
     index y is shift(A(shift(shift(E,y),0)),0). $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- B e. ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-integer-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- J e. ZZ $.
  ntp4vc-idle-cpu-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- L e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( K ` x )
      /\
      ( K ` x ) < ; ; 2 5 6
    ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < J
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( L ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( L ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < J
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < J
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( L ` x ) 0 ) ) y )
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
                  ( w ` ( NTP4VCShift ( L ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( L ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < J
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < J
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < J
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( L ` x ) 0 ) ) v )
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
    $e |- M e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- N e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- O e. ( NTP4VCAddr ^m NTP4VCAddr ) $.

  ntp4vc-size-properties $e |- (
    0 < J
    /\
    J <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-selected-cpu-idle $e |- ( K ` B ) =/= 0 $.
  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i-lt-size $e |- C < J $.
  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-i2-nonnegative $e |- 0 <_ B $.
  ntp4vc-i2-lt-size $e |- B < J $.
  ntp4vc-i1-le-size $e |- D <_ J $.
  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed H A ) $.
  ntp4vc-linked-allocation $e |- F e. I $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 B ) $.

  ntp4vc-smt-mask-pointer-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCShift ( L ` B ) 0 ) 1
  ) $.

  ntp4vc-idle-prefix $e |- A. x e. ZZ
    (
      (
        G
        `
        (
          NTP4VCShift
            ( A ` ( NTP4VCShift ( L ` B ) 0 ) )
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
          x < D
          ->
          ( K ` x ) =/= 0
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < J
        ->
        (
          NTP4VCValidRD F ( NTP4VCShift E x ) 1
          /\
          (
            NTP4VCValidRW
              F
              (
                NTP4VCShift
                  ( A ` ( NTP4VCShift ( NTP4VCShift E x ) 0 ) )
                  0
              )
              J
          )
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( M ` x ) 1
      /\
      (
        NTP4VCValidRD
          F
          ( NTP4VCShift ( A ` ( NTP4VCShift ( M ` x ) 0 ) ) 0 )
          J
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < J
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCShift ( A ` ( NTP4VCShift ( M ` x ) 0 ) ) 0 )
                  J
                  (
                    NTP4VCShift
                      (
                        A
                        `
                        (
                          NTP4VCShift
                            ( NTP4VCShift E y )
                            0
                        )
                      )
                      0
                  )
                  J
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( N ` x ) 1
      /\
      (
        NTP4VCValidRD
          F
          ( NTP4VCShift ( A ` ( NTP4VCShift ( N ` x ) 0 ) ) 0 )
          J
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < J
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCShift ( A ` ( NTP4VCShift ( N ` x ) 0 ) ) 0 )
                  J
                  (
                    NTP4VCShift
                      (
                        A
                        `
                        (
                          NTP4VCShift
                            ( NTP4VCShift E y )
                            0
                        )
                      )
                      0
                  )
                  J
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( O ` x ) 1
      /\
      (
        NTP4VCValidRD
          F
          ( NTP4VCShift ( A ` ( NTP4VCShift ( O ` x ) 0 ) ) 0 )
          J
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < J
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCShift ( A ` ( NTP4VCShift ( O ` x ) 0 ) ) 0 )
                  J
                  (
                    NTP4VCShift
                      (
                        A
                        `
                        (
                          NTP4VCShift
                            ( NTP4VCShift E y )
                            0
                        )
                      )
                      0
                  )
                  J
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
        x < J
        ->
        (
          NTP4VCValidRD F ( L ` x ) 1
          /\
          (
            NTP4VCValidRD
              F
              ( NTP4VCShift ( A ` ( NTP4VCShift ( L ` x ) 0 ) ) 0 )
              J
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < J
                  ->
                  (
                    NTP4VCSeparated
                      (
                        NTP4VCShift
                          ( A ` ( NTP4VCShift ( L ` x ) 0 ) )
                          0
                      )
                      J
                      (
                        NTP4VCShift
                          (
                            A
                            `
                            (
                              NTP4VCShift
                                ( NTP4VCShift E y )
                                0
                            )
                          )
                          0
                      )
                      J
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-is-core-idle-call-find-next-bit-pre-2-goal8 $a |- (
    NTP4VCValidRD
      F
      (
        NTP4VCShift
          ( A ` ( NTP4VCShift ( L ` B ) 0 ) )
          0
      )
      J
  ) $.
$}
