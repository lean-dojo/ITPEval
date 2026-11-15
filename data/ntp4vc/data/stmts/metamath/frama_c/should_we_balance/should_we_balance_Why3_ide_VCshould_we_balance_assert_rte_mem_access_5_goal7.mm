$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_5_goal7:
  the should-we-balance verification condition establishes one-unit read
  validity at offset three of the input structure, under the generated
  integer bounds, memory-validity, framing, linking, separation, and
  quantified scheduler-mask assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCFramed, NTP4VCSint32, NTP4VCUint32, and
  NTP4VCUint8 directly expand the corresponding source definitions.
  NTP4VCStorage expands the repeated zero-offset pointer lookup.

  The source let-bound values x, x_1, and a_2 through a_10 are retained by
  explicit conservative definitions. The arbitrary objects G through M
  represent, respectively, region, the extension of linked, l_size,
  l_sched_group_cpus, l_sched_group_mask, l_group_balance_mask, and
  l_cpu_smt_mask. The imported size property is an explicit hypothesis.

  Splitting the source curried implication chain into displayed hypotheses is
  bidirectionally equivalent to the original statement. Every quantified
  integer ranges over all of ZZ and every quantified address ranges over the
  full address type. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCStorage
  NTP4VCMaxSint32 NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8
  NTP4VCX NTP4VCX1 NTP4VCA2 NTP4VCA3 NTP4VCA4 NTP4VCA5
  NTP4VCA6 NTP4VCA7 NTP4VCA8 NTP4VCA9 NTP4VCA10
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

ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B C ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B ) $.

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

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) =
  ( NTP4VCShift A 4 ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) =
  ( A ` ( NTP4VCA2 B ) ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) =
  ( A ` ( NTP4VCShift ( NTP4VCA3 A B ) 0 ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A ) =
  ( NTP4VCShift A 1 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) =
  ( A ` ( NTP4VCA5 B ) ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA4 B C ) ( NTP4VCX A C ) )
  ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A ) =
  ( NTP4VCShift A 3 ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A ) =
  ( NTP4VCShift A 0 ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B ) =
  ( A ` ( NTP4VCA7 B ) ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B ) =
  ( NTP4VCShift ( NTP4VCA8 A B ) 0 ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B ) =
  ( NTP4VCShift ( NTP4VCA4 A B ) 0 ) $.

${
  $d x y z w v A B C D E F G H I J K L M N $.

  $( Source parameters:
     A=t_1, B=a_1, C=t_2, D=i, E=a, and F=t.
     G is region, H is the extension of linked, I is l_size,
     J is l_sched_group_cpus, K is l_sched_group_mask,
     L is l_group_balance_mask, and M is l_cpu_smt_mask. $)

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
  ntp4vc-idle-cpu-function $e |- N e. ( ZZ ^m ZZ ) $.

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


  ntp4vc-size-properties $e |- (
    0 < I
    /\
    I <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-x1-nonzero $e |- ( NTP4VCX1 A C B ) =/= 0 $.
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
  ntp4vc-a6-value-uint32 $e |- (
    NTP4VCUint32 ( A ` ( NTP4VCA6 B ) )
  ) $.
  ntp4vc-x-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX A B ) ) $.
  ntp4vc-a2-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA2 B ) 1
  ) $.
  ntp4vc-a5-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA5 B ) 1
  ) $.
  ntp4vc-a7-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA7 B ) 1
  ) $.
  ntp4vc-a3-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA3 C B ) 1
  ) $.
  ntp4vc-a1-field-two-valid-rd $e |- (
    NTP4VCValidRD F ( C ` ( NTP4VCShift B 2 ) ) 2
  ) $.
  ntp4vc-a8-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA8 C B ) 2
  ) $.
  ntp4vc-a8-field-one-sint32 $e |- (
    NTP4VCSint32
      ( A ` ( NTP4VCShift ( NTP4VCA8 C B ) 1 ) )
  ) $.
  ntp4vc-a9-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA9 C B ) 1
  ) $.
  ntp4vc-a9-target-valid-rd $e |- (
    NTP4VCValidRD F ( C ` ( NTP4VCA9 C B ) ) 1
  ) $.
  ntp4vc-x1-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCX1 A C B )
  ) $.
  ntp4vc-a10-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA10 C B ) I
  ) $.

  ntp4vc-a10-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < I
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA10 C B ) I
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

  ntp4vc-should-we-balance-assert-rte-mem-access-5-goal7 $a |- (
    NTP4VCValidRD F ( NTP4VCA6 B ) 1
  ) $.
$}
