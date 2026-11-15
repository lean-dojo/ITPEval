$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_assert_rte_mem_access_12_goal23:
  the should-we-balance verification condition establishes one-unit read
  validity at the zero-offset address reached through the fourth field of
  a_1, under the generated integer bounds, memory validity, havoc, framing,
  linking, separation, and quantified scheduler-mask assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. The named NTP4VC operations below expand the corresponding
  source definitions of shift, havoc, read/write validity, separation,
  framing, signed and unsigned integer ranges, and p_idle_core.

  The source let-bound expressions are retained by explicit conservative
  definitions or direct expansion. In particular, the source conclusion's
  a_5 = shift a_4 0 is expanded directly, while repeated later expressions
  retain exactly the source sharing and meaning. The arbitrary objects M, N,
  and P through V represent, respectively, region, the extension of linked,
  l_size, l_idle_cpu,
  l_sched_group_cpus, l_sched_group_mask, l_group_balance_mask,
  l_cpu_smt_mask, and land. The imported size property is an explicit
  hypothesis.

  Splitting the source curried implication chain into displayed hypotheses is
  bidirectionally equivalent to the original statement. Every quantified
  integer ranges over all of ZZ and every quantified address ranges over the
  full address type. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCStorage NTP4VCMaxSint32 NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8 NTP4VCIdleCore
  NTP4VCA2 NTP4VCX NTP4VCA3 NTP4VCA4 NTP4VCA5 NTP4VCA6
  NTP4VCX1 NTP4VCX2 NTP4VCA7 NTP4VCA8 NTP4VCA9 NTP4VCA10
  NTP4VCA11 NTP4VCA12 NTP4VCA13 NTP4VCA14 NTP4VCA15
  NTP4VCA16 NTP4VCA17 NTP4VCA18 NTP4VCA19 NTP4VCA20
  NTP4VCA21 NTP4VCA22 NTP4VCA23 NTP4VCA24
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
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

ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B ) $.
ntp4vc-a11-class $a class ( NTP4VCA11 A B ) $.
ntp4vc-a12-class $a class ( NTP4VCA12 A B ) $.
ntp4vc-a13-class $a class ( NTP4VCA13 A B C ) $.
ntp4vc-a14-class $a class ( NTP4VCA14 A B ) $.
ntp4vc-a15-class $a class ( NTP4VCA15 A B ) $.
ntp4vc-a16-class $a class ( NTP4VCA16 A B C ) $.
ntp4vc-a17-class $a class ( NTP4VCA17 A B C ) $.
ntp4vc-a18-class $a class ( NTP4VCA18 A B C D E F ) $.
ntp4vc-a19-class $a class ( NTP4VCA19 A B C ) $.
ntp4vc-a20-class $a class ( NTP4VCA20 A B C D E F ) $.
ntp4vc-a21-class $a class ( NTP4VCA21 A B C D E F G H ) $.
ntp4vc-a22-class $a class ( NTP4VCA22 A B C D E F G H I ) $.
ntp4vc-a23-class $a class ( NTP4VCA23 A B C D E F G ) $.
ntp4vc-a24-class $a class ( NTP4VCA24 A B C ) $.

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

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 3 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` ( NTP4VCA2 B ) ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 4 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) = ( A ` ( NTP4VCA3 B ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( A ` ( NTP4VCShift ( NTP4VCA4 A B ) 0 ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A ) = ( NTP4VCShift A 1 ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) = ( A ` ( NTP4VCA6 B ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA5 B C ) ( NTP4VCX1 A C ) )
  ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B ) =
  ( A ` ( NTP4VCA7 B ) ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B ) =
  ( NTP4VCShift ( NTP4VCA9 A B ) 1 ) $.
ntp4vc-a11-def $a |- ( NTP4VCA11 A B ) =
  ( NTP4VCShift ( NTP4VCA9 A B ) 0 ) $.
ntp4vc-a12-def $a |- ( NTP4VCA12 A B ) =
  ( A ` ( NTP4VCA11 A B ) ) $.
ntp4vc-a13-def $a |- ( NTP4VCA13 A B C ) =
  ( A ` ( NTP4VCA12 B C ) ) $.
ntp4vc-a14-def $a |- ( NTP4VCA14 A B ) =
  ( NTP4VCShift ( NTP4VCA5 A B ) 0 ) $.
ntp4vc-a15-def $a |- ( NTP4VCA15 A B ) =
  ( NTP4VCShift ( NTP4VCA8 A B ) 0 ) $.
ntp4vc-a16-def $a |- ( NTP4VCA16 A B C ) =
  ( A ` ( NTP4VCA15 B C ) ) $.
ntp4vc-a17-def $a |- ( NTP4VCA17 A B C ) =
  ( NTP4VCShift ( NTP4VCA16 A B C ) 0 ) $.
ntp4vc-a18-def $a |- ( NTP4VCA18 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA17 C D E ) F ) $.
ntp4vc-a19-def $a |- ( NTP4VCA19 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA13 B A C ) 0 )
  ) $.
ntp4vc-a20-def $a |- ( NTP4VCA20 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA17 C D E ) F ) $.
ntp4vc-a21-def $a |- ( NTP4VCA21 A B C D E F G H ) =
  (
    ( NTP4VCA20 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA5 C G ) H )
  ) $.
ntp4vc-a22-def $a |- ( NTP4VCA22 A B C D E F G H I ) =
  (
    ( NTP4VCA20 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA19 C G H ) I )
  ) $.
ntp4vc-a23-def $a |- ( NTP4VCA23 A B C D E F G ) =
  (
    ( NTP4VCA20 A B C D E F )
    `
    ( NTP4VCA10 C G )
  ) $.
ntp4vc-a24-def $a |- ( NTP4VCA24 A B C ) =
  ( NTP4VCShift ( NTP4VCA19 A B C ) 0 ) $.

${
  $d x y z w v A B C D E F G H I L M N P Q R S T U V $.

  $( Source parameters:
     A=a_1, B=t_3, C=t_4, D=a, E=i, F=t_1, G=t_2,
     H=i_1, I=i_2, and L=t. M is region, N is the extension of
     linked, P is l_size, Q is l_idle_cpu, R is l_sched_group_cpus,
     S is l_sched_group_mask, T is l_group_balance_mask,
     U is l_cpu_smt_mask, and V is land on integer pairs. $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t3-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t4-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-t1-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-i2-integer $e |- I e. ZZ $.
  ntp4vc-allocation-map $e |- L e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- N C_ ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- P e. ZZ $.
  ntp4vc-idle-cpu-function $e |- Q e. ( ZZ ^m ZZ ) $.
  ntp4vc-sched-group-cpus-function
    $e |- R e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- S e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- T e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- U e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-tl-idle-cpu $e |- A. x e. ZZ
    (
      0 <_ ( Q ` x )
      /\
      ( Q ` x ) < ; ; 2 5 6
    ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < P
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( U ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( U ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < P
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < P
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( U ` x ) 0 ) ) y )
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
                  ( w ` ( NTP4VCShift ( U ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( U ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < P
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < P
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < P
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( U ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.

  ntp4vc-land-function $e |- V e. ( ZZ ^m ( ZZ X. ZZ ) ) $.

  ntp4vc-size-properties $e |- (
    0 < P
    /\
    P <_ NTP4VCMaxSint32
  ) $.

  ntp4vc-x-not-two $e |- ( NTP4VCX B A ) =/= 2 $.
  ntp4vc-x2-nonzero $e |- ( NTP4VCX2 B C A ) =/= 0 $.
  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i-lt-size $e |- E < P $.
  ntp4vc-i2-nonnegative $e |- 0 <_ I $.
  ntp4vc-i2-le-size $e |- I <_ P $.
  ntp4vc-x1-nonnegative $e |- 0 <_ ( NTP4VCX1 B A ) $.
  ntp4vc-x1-lt-size $e |- ( NTP4VCX1 B A ) < P $.

  ntp4vc-region-a $e |- ( M ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( M ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed M C ) $.
  ntp4vc-linked-allocation $e |- L e. N $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 I ) $.
  ntp4vc-a1-valid-rd $e |- ( NTP4VCValidRD L A 5 ) $.
  ntp4vc-x-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX B A ) ) $.
  ntp4vc-x1-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX1 B A ) ) $.
  ntp4vc-a3-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA3 A ) 1 ) $.
  ntp4vc-a6-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA6 A ) 1 ) $.
  ntp4vc-a2-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA2 A ) 1 ) $.
  ntp4vc-a7-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA7 A ) 1 ) $.
  ntp4vc-a8-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA8 D E ) 1 ) $.
  ntp4vc-a4-valid-rd $e |- ( NTP4VCValidRD L ( NTP4VCA4 C A ) 1 ) $.
  ntp4vc-a1-field-valid-rd $e |- (
    NTP4VCValidRD L ( C ` ( NTP4VCShift A 2 ) ) 2
  ) $.
  ntp4vc-a9-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA9 C A ) 2
  ) $.
  ntp4vc-a10-value-sint32 $e |- (
    NTP4VCSint32 ( B ` ( NTP4VCA10 C A ) )
  ) $.
  ntp4vc-a11-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA11 C A ) 1
  ) $.
  ntp4vc-a12-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA12 C A ) 1
  ) $.
  ntp4vc-a13-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA13 T C A ) 1
  ) $.
  ntp4vc-x2-uint8 $e |- ( NTP4VCUint8 ( NTP4VCX2 B C A ) ) $.
  ntp4vc-a14-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA14 C A ) P
  ) $.
  ntp4vc-a17-valid-rw $e |- (
    NTP4VCValidRW L ( NTP4VCA17 C D E ) P
  ) $.

  ntp4vc-a18-a5-minus-one-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCA18 F B C D E P )
        `
        ( NTP4VCShift ( NTP4VCA5 C A ) ( -u 1 ) )
      )
  ) $.

  ntp4vc-a18-a19-minus-one-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCA18 F B C D E P )
        `
        ( NTP4VCShift ( NTP4VCA19 C T A ) ( -u 1 ) )
      )
  ) $.

  ntp4vc-a21-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA21 G B C D E P A H )
  ) $.
  ntp4vc-a22-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA22 G B C D E P T A H )
  ) $.
  ntp4vc-a18-a10-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCA18 F B C D E P ) ` ( NTP4VCA10 C A ) )
  ) $.
  ntp4vc-a23-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA23 G B C D E P A )
  ) $.
  ntp4vc-a24-valid-rd $e |- (
    NTP4VCValidRD L ( NTP4VCA24 C T A ) P
  ) $.
  ntp4vc-a17-a24-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCA17 C D E ) P
      ( NTP4VCA24 C T A ) P
  ) $.

  ntp4vc-land-branch $e |- (
    ( V ` <. 7 , ( NTP4VCA23 G B C D E P A ) >. ) =/= 0
    ->
    H = ( -u 1 )
  ) $.

  ntp4vc-i1-found-properties $e |- (
    H =/= ( -u 1 )
    ->
    (
      ( Q ` H ) =/= 0
      /\
      (
        ( NTP4VCA21 G B C D E P A H ) =/= 0
        /\
        (
          ( NTP4VCA22 G B C D E P T A H ) =/= 0
          /\
          (
            0 <_ H
            /\
            H < P
          )
        )
      )
    )
  ) $.

  ntp4vc-i1-minus-one-mask-transfer $e |- (
    H = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA20 G B C D E P )
          `
          ( NTP4VCShift ( NTP4VCA19 C T A ) x )
        )
        =/=
        0
        ->
        (
          0 <_ x
          ->
          (
            x < P
            ->
            (
              ( NTP4VCA20 G B C D E P )
              `
              ( NTP4VCShift ( NTP4VCA16 C D E ) x )
            )
            =/=
            0
          )
        )
      )
  ) $.

  ntp4vc-i1-prefix-idle $e |- (
    H =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA20 G B C D E P )
          `
          ( NTP4VCShift ( NTP4VCA5 C A ) x )
        )
        =/=
        0
        ->
        (
          (
            ( NTP4VCA20 G B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA19 C T A ) x )
          )
          =/=
          0
          ->
          (
            0 <_ x
            ->
            (
              x < H
              ->
              (
                x < P
                ->
                ( Q ` x ) = 0
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-i2-prefix-idle $e |- (
    H = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA20 G B C D E P )
          `
          ( NTP4VCShift ( NTP4VCA5 C A ) x )
        )
        =/=
        0
        ->
        (
          (
            ( NTP4VCA20 G B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA19 C T A ) x )
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
              (
                x < P
                ->
                ( Q ` x ) = 0
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-i1-to-i2-not-idle-core $e |- (
    H =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA20 G B C D E P )
          `
          ( NTP4VCShift ( NTP4VCA5 C A ) x )
        )
        =/=
        0
        ->
        (
          (
            ( NTP4VCA20 G B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA19 C T A ) x )
          )
          =/=
          0
          ->
          (
            0 <_ x
            ->
            (
              H <_ x
              ->
              (
                x < I
                ->
                (
                  x < P
                  ->
                  -. (
                    NTP4VCIdleCore
                      C
                      ( NTP4VCA20 G B C D E P )
                      x P U Q
                  )
                )
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-found-or-not-idle-core $e |- (
    H =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA20 G B C D E P )
          `
          ( NTP4VCShift ( NTP4VCA19 C T A ) x )
        )
        =/=
        0
        ->
        (
          0 <_ x
          ->
          (
            x < P
            ->
            (
              (
                ( NTP4VCA20 G B C D E P )
                `
                ( NTP4VCShift ( NTP4VCA16 C D E ) x )
              )
              =/=
              0
              \/
              -. (
                NTP4VCIdleCore
                  C
                  ( NTP4VCA20 G B C D E P )
                  x P U Q
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-a14-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < P
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA14 C A ) P
            ( NTP4VCStorage C ( NTP4VCShift D x ) ) P
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < P
        ->
        (
          NTP4VCValidRD L ( NTP4VCShift D x ) 1
          /\
          (
            NTP4VCValidRW
              L
              ( NTP4VCStorage C ( NTP4VCShift D x ) )
              P
          )
        )
      )
    ) $.

  ntp4vc-a18-mask-equivalence $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < P
        ->
        (
          (
            ( NTP4VCA18 F B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA19 C T A ) x )
          )
          =/=
          0
          <->
          (
            ( NTP4VCA18 F B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA16 C D E ) x )
          )
          =/=
          0
        )
      )
    ) $.

  ntp4vc-a20-mask-transfer $e |- A. x e. ZZ
    (
      (
        ( NTP4VCA20 G B C D E P )
        `
        ( NTP4VCShift ( NTP4VCA16 C D E ) x )
      )
      =/=
      0
      ->
      (
        0 <_ x
        ->
        (
          x < P
          ->
          (
            ( NTP4VCA20 G B C D E P )
            `
            ( NTP4VCShift ( NTP4VCA19 C T A ) x )
          )
          =/=
          0
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD L ( R ` x ) 1
      /\
      (
        NTP4VCValidRD L ( NTP4VCStorage C ( R ` x ) ) P
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < P
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( R ` x ) ) P
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) P
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD L ( S ` x ) 1
      /\
      (
        NTP4VCValidRD L ( NTP4VCStorage C ( S ` x ) ) P
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < P
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( S ` x ) ) P
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) P
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      NTP4VCValidRD L ( T ` x ) 1
      /\
      (
        NTP4VCValidRD L ( NTP4VCStorage C ( T ` x ) ) P
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < P
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage C ( T ` x ) ) P
                  ( NTP4VCStorage C ( NTP4VCShift D y ) ) P
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
        x < P
        ->
        (
          NTP4VCValidRD L ( U ` x ) 1
          /\
          (
            NTP4VCValidRD L ( NTP4VCStorage C ( U ` x ) ) P
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < P
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage C ( U ` x ) ) P
                      ( NTP4VCStorage C ( NTP4VCShift D y ) ) P
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-should-we-balance-assert-rte-mem-access-12-goal23 $a |- (
    NTP4VCValidRD L ( NTP4VCShift ( NTP4VCA4 C A ) 0 ) 1
  ) $.
$}
