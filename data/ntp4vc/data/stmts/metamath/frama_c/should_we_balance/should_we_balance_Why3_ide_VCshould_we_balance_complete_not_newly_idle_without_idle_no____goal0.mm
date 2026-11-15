$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_complete_not_newly_idle_without_idle_no____goal0:
  the should-we-balance verification condition classifies completion into the
  generated zero, newly-idle, idle-core, non-idle-core, and idle-CPU cases
  under integer bounds, memory validity, framing, linking, separation, and
  quantified scheduler-mask assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCStorage, NTP4VCValidRD,
  NTP4VCValidRW, NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32,
  NTP4VCUint32, NTP4VCUint8, and NTP4VCIdleCore directly expand the
  corresponding source definitions.

  The source let-bound values x, x_1, x_2, x_3, x_4 and a_2 through a_7 are
  retained by explicit conservative definitions. The arbitrary objects G
  through O represent, respectively, region, the extension of linked,
  l_size, l_sched_group_cpus, l_sched_group_mask, l_group_balance_mask,
  l_cpu_smt_mask, l_idle_cpu, and land on integer pairs. The imported size
  property is an explicit hypothesis.

  Splitting the source curried implication chain into displayed hypotheses is
  bidirectionally equivalent to the original statement. Every quantified
  integer ranges over all of ZZ and every quantified address ranges over the
  full address type. The existential witnesses remain internal to the
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCStorage
  NTP4VCMaxSint32 NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8 NTP4VCIdleCore
  NTP4VCX NTP4VCX1 NTP4VCA2 NTP4VCA3 NTP4VCX2
  NTP4VCA4 NTP4VCA5 NTP4VCX3 NTP4VCA6 NTP4VCA7 NTP4VCX4
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
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
ntp4vc-idle-core-syntax
  $a wff ( NTP4VCIdleCore A B C D E F ) $.

ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B C ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
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
  $d x A B C D E F $.
  ntp4vc-idle-core-def $a |- (
    ( NTP4VCIdleCore A B C D E F )
    <->
    A. x e. ZZ
      (
        (
          B
          `
          (
            NTP4VCShift
              ( A ` ( NTP4VCShift ( E ` C ) 0 ) )
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
            ( F ` x ) =/= 0
          )
        )
      )
  ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A B ) =
  ( A ` ( NTP4VCShift B 1 ) ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) =
  ( A ` ( NTP4VCShift B 3 ) ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) =
  ( A ` ( NTP4VCShift B 4 ) ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) =
  ( A ` ( NTP4VCShift B 0 ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA3 B C ) 1 ) ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) =
  ( A ` ( NTP4VCShift ( NTP4VCA3 A B ) 0 ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( A ` ( NTP4VCShift ( NTP4VCA2 A B ) 0 ) ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA5 B C ) ( NTP4VCX A C ) )
  ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B ) =
  ( NTP4VCShift ( NTP4VCA5 A B ) 0 ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A B C ) =
  (
    A
    `
    (
      NTP4VCShift
        ( B ` ( NTP4VCA4 A C ) )
        0
    )
  ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A B C D ) =
  ( A ` <. 7 , ( NTP4VCX2 B C D ) >. ) $.

${
  $d x y z w v A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=t_1, B=a_1, C=t_2, D=i, E=a, and F=t.
     G is region, H is the extension of linked, I is l_size,
     J is l_sched_group_cpus, K is l_sched_group_mask,
     L is l_group_balance_mask, M is l_cpu_smt_mask,
     N is l_idle_cpu, and O is land on integer pairs. $)

  ntp4vc-t1-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t2-pointer-map
    $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- I e. ZZ $.
  ntp4vc-sched-group-cpus-function
    $e |- J e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- K e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- L e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- M e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( N ` x )
      /\
      ( N ` x ) < ; ; 2 5 6
    ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < I
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( M ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( M ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < I
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < I
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

  itpeval-q-mask-trans $e |- A. w e. ( NTP4VCAddr ^m NTP4VCAddr )
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
                    x < I
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < I
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < I
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

  ntp4vc-idle-cpu-function $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-land-function $e |- O e. ( ZZ ^m ( ZZ X. ZZ ) ) $.

  ntp4vc-size-properties $e |- (
    0 < I
    /\
    I <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ D $.
  ntp4vc-i-lt-size $e |- D < I $.
  ntp4vc-x-nonnegative $e |- 0 <_ ( NTP4VCX A B ) $.
  ntp4vc-x-lt-size $e |- ( NTP4VCX A B ) < I $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( G ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed G C ) $.
  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-a1-valid-rd $e |- ( NTP4VCValidRD F B 5 ) $.
  ntp4vc-x1-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX1 A B ) ) $.
  ntp4vc-x-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX A B ) ) $.
  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA2 C B ) 1
  ) $.
  ntp4vc-a1-field-two-valid-rd $e |- (
    NTP4VCValidRD F ( C ` ( NTP4VCShift B 2 ) ) 2
  ) $.
  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA3 C B ) 2
  ) $.
  ntp4vc-x2-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX2 A C B )
  ) $.
  ntp4vc-a4-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA4 C B ) 1
  ) $.
  ntp4vc-x3-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCX3 A C B )
  ) $.
  ntp4vc-a6-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA6 C B ) I
  ) $.

  ntp4vc-a6-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < I
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA6 C B ) I
            ( NTP4VCStorage C ( NTP4VCShift E x ) ) I
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < I
        ->
        (
          NTP4VCValidRD F ( NTP4VCShift E x ) 1
          /\
          (
            NTP4VCValidRW
              F
              ( NTP4VCStorage C ( NTP4VCShift E x ) )
              I
          )
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( J ` x ) 1
      /\
      (
        NTP4VCValidRD F ( NTP4VCStorage C ( J ` x ) ) I
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < I
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( J ` x ) ) I
                  ( NTP4VCStorage C ( NTP4VCShift E y ) ) I
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( K ` x ) 1
      /\
      (
        NTP4VCValidRD F ( NTP4VCStorage C ( K ` x ) ) I
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < I
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( K ` x ) ) I
                  ( NTP4VCStorage C ( NTP4VCShift E y ) ) I
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD F ( L ` x ) 1
      /\
      (
        NTP4VCValidRD F ( NTP4VCStorage C ( L ` x ) ) I
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < I
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( L ` x ) ) I
                  ( NTP4VCStorage C ( NTP4VCShift E y ) ) I
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
        x < I
        ->
        (
          NTP4VCValidRD F ( M ` x ) 1
          /\
          (
            NTP4VCValidRD F ( NTP4VCStorage C ( M ` x ) ) I
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < I
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage C ( M ` x ) ) I
                      ( NTP4VCStorage C ( NTP4VCShift E y ) ) I
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-should-we-balance-complete-not-newly-idle-without-idle-no-goal0
    $a |- (
      ( NTP4VCX3 A C B ) = 0
      \/
      (
        (
          ( NTP4VCX1 A B ) = 2
          /\
          ( NTP4VCX3 A C B ) =/= 0
        )
        \/
        (
          (
            ( NTP4VCX1 A B ) =/= 2
            /\
            (
              ( NTP4VCX3 A C B ) =/= 0
              /\
              A. x e. ZZ
                (
                  ( A ` ( NTP4VCShift ( NTP4VCA5 C B ) x ) ) =/= 0
                  ->
                  (
                    ( A ` ( NTP4VCShift ( NTP4VCA7 C L B ) x ) ) =/= 0
                    ->
                    (
                      0 <_ x
                      ->
                      (
                        x < I
                        ->
                        ( N ` x ) = 0
                      )
                    )
                  )
                )
            )
          )
          \/
          (
            (
              ( NTP4VCX1 A B ) =/= 2
              /\
              (
                ( NTP4VCX4 O A C B ) = 0
                /\
                (
                  ( NTP4VCX3 A C B ) =/= 0
                  /\
                  E. x e. ZZ
                    (
                      (
                        ( A ` ( NTP4VCShift ( NTP4VCA5 C B ) x ) )
                        =/=
                        0
                      )
                      /\
                      (
                        (
                          A
                          `
                          ( NTP4VCShift ( NTP4VCA7 C L B ) x )
                        )
                        =/=
                        0
                        /\
                        (
                          0 <_ x
                          /\
                          (
                            x < I
                            /\
                            ( NTP4VCIdleCore C A x I M N )
                          )
                        )
                      )
                    )
                )
              )
            )
            \/
            (
              (
                ( NTP4VCX1 A B ) =/= 2
                /\
                (
                  ( NTP4VCX4 O A C B ) =/= 0
                  /\
                  (
                    ( NTP4VCX3 A C B ) =/= 0
                    /\
                    E. x e. ZZ
                      (
                        ( N ` x ) =/= 0
                        /\
                        (
                          (
                            A
                            `
                            ( NTP4VCShift ( NTP4VCA5 C B ) x )
                          )
                          =/=
                          0
                          /\
                          (
                            (
                              A
                              `
                              ( NTP4VCShift ( NTP4VCA7 C L B ) x )
                            )
                            =/=
                            0
                            /\
                            (
                              0 <_ x
                              /\
                              x < I
                            )
                          )
                        )
                      )
                  )
                )
              )
              \/
              (
                ( NTP4VCX1 A B ) =/= 2
                /\
                (
                  ( NTP4VCX4 O A C B ) = 0
                  /\
                  (
                    ( NTP4VCX3 A C B ) =/= 0
                    /\
                    (
                      A. x e. ZZ
                        (
                          (
                            A
                            `
                            ( NTP4VCShift ( NTP4VCA5 C B ) x )
                          )
                          =/=
                          0
                          ->
                          (
                            (
                              A
                              `
                              ( NTP4VCShift ( NTP4VCA7 C L B ) x )
                            )
                            =/=
                            0
                            ->
                            (
                              0 <_ x
                              ->
                              (
                                x < I
                                ->
                                -. ( NTP4VCIdleCore C A x I M N )
                              )
                            )
                          )
                        )
                      /\
                      E. y e. ZZ
                        (
                          ( N ` y ) =/= 0
                          /\
                          (
                            (
                              A
                              `
                              ( NTP4VCShift ( NTP4VCA5 C B ) y )
                            )
                            =/=
                            0
                            /\
                            (
                              (
                                A
                                `
                                ( NTP4VCShift ( NTP4VCA7 C L B ) y )
                              )
                              =/=
                              0
                              /\
                              (
                                0 <_ y
                                /\
                                y < I
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
      )
    ) $.
$}
