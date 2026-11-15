$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_preserved_goal11:
  the should-we-balance verification condition preserves the loop invariant
  lower bound -1 <= i_3 under the generated integer bounds, branch and scan
  invariants, memory validity, framing, linking, separation, havoc updates,
  and quantified scheduler-mask assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. The named operations below explicitly define source shift,
  havoc, read/write validity, separation, framing, the idle-core predicate,
  and the C integer ranges. Every source let-bound value x, a_3 through a_30,
  and x_1 through x_5 is retained by an explicit definition.

  N is the source allocation map t. The arbitrary objects P through X
  represent region, the extension of linked, to_uint32, l_size, l_idle_cpu,
  l_sched_group_cpus, l_sched_group_mask, l_group_balance_mask, and
  l_cpu_smt_mask as documented in the parameter block. NTP4VCDualWitness
  preserves the source existential witness internally over all of ZZ.
  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent to the original statement. Every
  integer and address quantifier retains its full source domain. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCStorage NTP4VCMaxSint32 NTP4VCMaxIndex NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8 NTP4VCIdleCore
  NTP4VCDualWitness
  NTP4VCX NTP4VCA3 NTP4VCX1 NTP4VCA4 NTP4VCA5 NTP4VCA6
  NTP4VCA7 NTP4VCA8 NTP4VCX2 NTP4VCX3 NTP4VCA9 NTP4VCA10
  NTP4VCA11 NTP4VCA12 NTP4VCA13 NTP4VCA14 NTP4VCX4
  NTP4VCA15 NTP4VCA16 NTP4VCA17 NTP4VCA18 NTP4VCA19
  NTP4VCA20 NTP4VCA21 NTP4VCA22 NTP4VCA23 NTP4VCA24
  NTP4VCA25 NTP4VCA26 NTP4VCA27 NTP4VCA28 NTP4VCA29
  NTP4VCA30 NTP4VCX5
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
ntp4vc-dual-witness-syntax
  $a wff ( NTP4VCDualWitness A B C D E ) $.

ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B C ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B ) $.
ntp4vc-a11-class $a class ( NTP4VCA11 A B ) $.
ntp4vc-a12-class $a class ( NTP4VCA12 A B ) $.
ntp4vc-a13-class $a class ( NTP4VCA13 A ) $.
ntp4vc-a14-class $a class ( NTP4VCA14 A B ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A B C ) $.
ntp4vc-a15-class $a class ( NTP4VCA15 A B ) $.
ntp4vc-a16-class $a class ( NTP4VCA16 A B ) $.
ntp4vc-a17-class $a class ( NTP4VCA17 A B ) $.
ntp4vc-a18-class $a class ( NTP4VCA18 A B C ) $.
ntp4vc-a19-class $a class ( NTP4VCA19 A B C ) $.
ntp4vc-a20-class $a class ( NTP4VCA20 A B C ) $.
ntp4vc-a21-class $a class ( NTP4VCA21 A B ) $.
ntp4vc-a22-class $a class ( NTP4VCA22 A B C D E F ) $.
ntp4vc-a23-class $a class ( NTP4VCA23 A B C ) $.
ntp4vc-a24-class $a class ( NTP4VCA24 A B C D E F ) $.
ntp4vc-a25-class $a class ( NTP4VCA25 A B C D E F G ) $.
ntp4vc-a26-class $a class ( NTP4VCA26 A B C D E F G H ) $.
ntp4vc-a27-class $a class ( NTP4VCA27 A B C D E F G H ) $.
ntp4vc-a28-class $a class ( NTP4VCA28 A B C D E F G H I ) $.
ntp4vc-a29-class $a class ( NTP4VCA29 A B C D E F G ) $.
ntp4vc-a30-class $a class ( NTP4VCA30 A B C ) $.
ntp4vc-x5-class $a class ( NTP4VCX5 A B ) $.

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
          B ` ( NTP4VCShift ( A ` ( NTP4VCShift ( E ` C ) 0 ) ) x )
        ) =/= 0
        ->
        ( 0 <_ x -> ( x < D -> ( F ` x ) =/= 0 ) )
      )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-dual-witness-def $a |- (
    ( NTP4VCDualWitness A B C D E )
    <->
    E. x e. ZZ
      (
        ( A ` ( NTP4VCShift B x ) ) =/= 0
        /\
        (
          ( A ` ( NTP4VCShift C x ) ) =/= 0
          /\
          ( x < D /\ E <_ x )
        )
      )
  ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` B ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 3 ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) =
  ( A ` ( NTP4VCA3 B ) ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A ) = ( NTP4VCShift A 4 ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( A ` ( NTP4VCA4 B ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B ) =
  ( NTP4VCShift ( NTP4VCA5 A B ) 0 ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A B ) =
  ( A ` ( NTP4VCA6 A B ) ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A ) = ( NTP4VCShift A 1 ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) =
  ( A ` ( NTP4VCA8 B ) ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA7 B C ) ( NTP4VCX2 A C ) ) ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B ) =
  ( NTP4VCShift A B ) $.
ntp4vc-a11-def $a |- ( NTP4VCA11 A B ) =
  ( A ` ( NTP4VCA9 B ) ) $.
ntp4vc-a12-def $a |- ( NTP4VCA12 A B ) =
  ( NTP4VCShift ( NTP4VCA11 A B ) 1 ) $.
ntp4vc-a13-def $a |- ( NTP4VCA13 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a14-def $a |- ( NTP4VCA14 A B ) =
  ( NTP4VCShift ( A ` ( NTP4VCA13 B ) ) 1 ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A B C ) =
  ( A ` ( NTP4VCA14 B C ) ) $.
ntp4vc-a15-def $a |- ( NTP4VCA15 A B ) =
  ( NTP4VCShift ( NTP4VCA10 A B ) 0 ) $.
ntp4vc-a16-def $a |- ( NTP4VCA16 A B ) =
  ( NTP4VCShift ( NTP4VCA11 A B ) 0 ) $.
ntp4vc-a17-def $a |- ( NTP4VCA17 A B ) =
  ( A ` ( NTP4VCA16 A B ) ) $.
ntp4vc-a18-def $a |- ( NTP4VCA18 A B C ) =
  ( A ` ( NTP4VCA17 B C ) ) $.
ntp4vc-a19-def $a |- ( NTP4VCA19 A B C ) =
  ( A ` ( NTP4VCA15 B C ) ) $.
ntp4vc-a20-def $a |- ( NTP4VCA20 A B C ) =
  ( NTP4VCShift ( NTP4VCA19 A B C ) 0 ) $.
ntp4vc-a21-def $a |- ( NTP4VCA21 A B ) =
  ( NTP4VCShift ( NTP4VCA7 A B ) 0 ) $.
ntp4vc-a22-def $a |- ( NTP4VCA22 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA20 C D E ) F ) $.
ntp4vc-a23-def $a |- ( NTP4VCA23 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA18 B A C ) 0 ) ) $.
ntp4vc-a24-def $a |- ( NTP4VCA24 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA20 C D E ) F ) $.
ntp4vc-a25-def $a |- ( NTP4VCA25 A B C D E F G ) =
  (
    ( NTP4VCA24 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA19 C D E ) G )
  ) $.
ntp4vc-a26-def $a |- ( NTP4VCA26 A B C D E F G H ) =
  (
    ( NTP4VCA24 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA7 C G ) H )
  ) $.
ntp4vc-a27-def $a |- ( NTP4VCA27 A B C D E F G H ) =
  (
    ( NTP4VCA24 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA7 C G ) H )
  ) $.
ntp4vc-a28-def $a |- ( NTP4VCA28 A B C D E F G H I ) =
  (
    ( NTP4VCA24 A B C D E F )
    `
    ( NTP4VCShift ( NTP4VCA23 C G H ) I )
  ) $.
ntp4vc-a29-def $a |- ( NTP4VCA29 A B C D E F G ) =
  ( ( NTP4VCA24 A B C D E F ) ` ( NTP4VCA12 C G ) ) $.
ntp4vc-a30-def $a |- ( NTP4VCA30 A B C ) =
  ( NTP4VCShift ( NTP4VCA23 A B C ) 0 ) $.
ntp4vc-x5-def $a |- ( NTP4VCX5 A B ) = ( A ` B ) $.

${
  $d x y z w v A B C D E F G H I J K L M N O P Q R S T U V W X $.

  $( Source parameters:
     A=i_3, B=a_1, C=t_3, D=t_5, E=a, F=i, G=a_2, H=t_4,
     I=t_1, J=t_2, K=i_1, L=i_4, M=i_2, N=t, and O=p.
     P is region, Q is the extension of linked, R is to_uint32,
     S is l_size, T is l_idle_cpu, U is l_sched_group_cpus,
     V is l_sched_group_mask, W is l_group_balance_mask, and
     X is l_cpu_smt_mask. $)

  ntp4vc-i3-integer $e |- A e. ZZ $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t3-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t5-pointer-map $e |- D e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-a2-address $e |- G e. NTP4VCAddr $.
  ntp4vc-t4-memory $e |- H e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t1-memory $e |- I e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- J e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- K e. ZZ $.
  ntp4vc-i4-integer $e |- L e. ZZ $.
  ntp4vc-i2-integer $e |- M e. ZZ $.
  ntp4vc-allocation-map $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-p-boolean $e |- O e. 2o $.

  ntp4vc-region-map $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- Q C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- S e. ZZ $.
  ntp4vc-idle-cpu-function $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-sched-group-cpus-function
    $e |- U e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- V e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- W e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- X e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < S
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( X ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( X ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < S
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < S
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( X ` x ) 0 ) ) y )
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
                  ( w ` ( NTP4VCShift ( X ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( X ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < S
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < S
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < S
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( X ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.


  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( R ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( R ` x ) = x ) $.
  ntp4vc-size-properties $e |- ( 0 < S /\ S <_ NTP4VCMaxSint32 ) $.
  ntp4vc-idle-cpu-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( T ` x ) ) $.

  ntp4vc-idle-i3-iff-i2-nonzero $e |- (
    ( ( NTP4VCX T A ) =/= 0 ) <-> ( M =/= 0 )
  ) $.
  ntp4vc-x1-not-two $e |- ( NTP4VCX1 C B ) =/= 2 $.
  ntp4vc-x3-nonzero $e |- ( NTP4VCX3 C D B ) =/= 0 $.
  ntp4vc-i-nonnegative $e |- 0 <_ F $.
  ntp4vc-i-lt-size $e |- F < S $.
  ntp4vc-i3-nonnegative $e |- 0 <_ A $.
  ntp4vc-i3-lt-size $e |- A < S $.
  ntp4vc-i4-nonnegative $e |- 0 <_ L $.
  ntp4vc-i4-le-size $e |- L <_ S $.
  ntp4vc-converted-i3-lt-size $e |- ( R ` A ) < S $.
  ntp4vc-x2-nonnegative $e |- 0 <_ ( NTP4VCX2 C B ) $.
  ntp4vc-x2-lt-size $e |- ( NTP4VCX2 C B ) < S $.
  ntp4vc-region-a $e |- ( P ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( P ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed P D ) $.
  ntp4vc-linked-allocation $e |- N e. Q $.
  ntp4vc-i2-uint8 $e |- ( NTP4VCUint8 M ) $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 K ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 A ) $.
  ntp4vc-i4-sint32 $e |- ( NTP4VCSint32 L ) $.
  ntp4vc-a1-valid-rd $e |- ( NTP4VCValidRD N B 5 ) $.
  ntp4vc-x1-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX1 C B ) ) $.
  ntp4vc-i3-successor-sint32 $e |- ( NTP4VCSint32 ( 1 + A ) ) $.
  ntp4vc-x2-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX2 C B ) ) $.
  ntp4vc-a4-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA4 B ) 1 ) $.
  ntp4vc-a8-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA8 B ) 1 ) $.
  ntp4vc-a3-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA3 B ) 1 ) $.
  ntp4vc-a9-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA9 B ) 1 ) $.
  ntp4vc-a10-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA10 E F ) 1 ) $.
  ntp4vc-a5-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA5 D B ) 1 ) $.
  ntp4vc-a1-field-valid-rd $e |- (
    NTP4VCValidRD N ( D ` ( NTP4VCShift B 2 ) ) 2
  ) $.
  ntp4vc-a11-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA11 D B ) 2 ) $.
  ntp4vc-a12-value-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCA12 D B ) )
  ) $.
  ntp4vc-x4-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX4 H D G ) ) $.
  ntp4vc-a15-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA15 E F ) 1 ) $.
  ntp4vc-a6-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA6 D B ) 1 ) $.
  ntp4vc-a16-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA16 D B ) 1 ) $.
  ntp4vc-a17-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA17 D B ) 1 ) $.
  ntp4vc-a18-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA18 W D B ) 1
  ) $.
  ntp4vc-x3-uint8 $e |- ( NTP4VCUint8 ( NTP4VCX3 C D B ) ) $.
  ntp4vc-a20-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA20 D E F ) S
  ) $.
  ntp4vc-a21-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA21 D B ) S
  ) $.
  ntp4vc-a20-valid-rw $e |- (
    NTP4VCValidRW N ( NTP4VCA20 D E F ) S
  ) $.

  ntp4vc-a22-a7-minus-one-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCA22 I C D E F S )
        `
        ( NTP4VCShift ( NTP4VCA7 D B ) ( -u 1 ) )
      )
  ) $.
  ntp4vc-a22-a23-minus-one-uint8 $e |- (
    NTP4VCUint8
      (
        ( NTP4VCA22 I C D E F S )
        `
        ( NTP4VCShift ( NTP4VCA23 D W B ) ( -u 1 ) )
      )
  ) $.
  ntp4vc-a25-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA25 J C D E F S A )
  ) $.
  ntp4vc-a26-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA26 J C D E F S B K )
  ) $.
  ntp4vc-a27-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA27 J C D E F S B A )
  ) $.
  ntp4vc-a28-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA28 J C D E F S W B K )
  ) $.
  ntp4vc-a22-a12-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCA22 I C D E F S ) ` ( NTP4VCA12 D B ) )
  ) $.
  ntp4vc-a29-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA29 J C D E F S B )
  ) $.
  ntp4vc-a30-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA30 D W B ) S
  ) $.
  ntp4vc-a20-a30-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCA20 D E F ) S ( NTP4VCA30 D W B ) S
  ) $.

  ntp4vc-source-branch $e |- (
    (
      M = 0
      ->
      A <_ NTP4VCMaxIndex
    )
    /\
    (
      M =/= 0
      ->
      (
        O = 0
        /\
        (
          G = B
          /\
          (
            ( NTP4VCX T A ) =/= 0
            /\
            (
              ( ( NTP4VCX4 H D G ) mod 8 ) = 0
              /\
              (
                ( NTP4VCA24 J C D E F S ) = H
                /\
                (
                  A <_ NTP4VCMaxIndex
                  /\
                  (
                    -. ( NTP4VCIdleCore D H A S X T )
                    /\
                    (
                      ( NTP4VCValidRD N ( NTP4VCA13 G ) 1 )
                      /\
                      ( NTP4VCValidRD N ( NTP4VCA14 D G ) 1 )
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

  ntp4vc-land-branch $e |- (
    ( ( NTP4VCA29 J C D E F S B ) mod 8 ) =/= 0
    ->
    K = ( -u 1 )
  ) $.

  ntp4vc-i1-found-properties $e |- (
    K =/= ( -u 1 )
    ->
    (
      ( T ` K ) =/= 0
      /\
      (
        ( NTP4VCA26 J C D E F S B K ) =/= 0
        /\
        (
          ( NTP4VCA28 J C D E F S W B K ) =/= 0
          /\
          ( 0 <_ K /\ K < S )
        )
      )
    )
  ) $.

  ntp4vc-no-i1-transfers-mask $e |- (
    K = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA24 J C D E F S )
          `
          ( NTP4VCShift ( NTP4VCA23 D W B ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < S
            ->
            (
              ( NTP4VCA24 J C D E F S )
              `
              ( NTP4VCShift ( NTP4VCA19 D E F ) x )
            ) =/= 0
          )
        )
      )
  ) $.

  ntp4vc-dual-witness-lower-bound $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA24 J C D E F S )
        ( NTP4VCA19 D E F ) ( NTP4VCA7 D B )
        S ( NTP4VCX5 R L )
    )
    ->
    ( NTP4VCX5 R L ) <_ A
  ) $.

  ntp4vc-dual-witness-selected-nonzero $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA24 J C D E F S )
        ( NTP4VCA19 D E F ) ( NTP4VCA7 D B )
        S ( NTP4VCX5 R L )
    )
    ->
    (
      ( NTP4VCA25 J C D E F S A ) =/= 0
      /\
      ( NTP4VCA27 J C D E F S B A ) =/= 0
    )
  ) $.

  ntp4vc-all-tail-zero-implies-i3-is-size $e |- (
    (
      A. x e. ZZ
        (
          x < S
          ->
          (
            ( NTP4VCX5 R L ) <_ x
            ->
            (
              (
                ( NTP4VCA24 J C D E F S )
                `
                ( NTP4VCShift ( NTP4VCA19 D E F ) x )
              ) = 0
              \/
              (
                ( NTP4VCA24 J C D E F S )
                `
                ( NTP4VCShift ( NTP4VCA7 D B ) x )
              ) = 0
            )
          )
        )
    )
    ->
    S = A
  ) $.

  ntp4vc-prefix-idle-before-i1 $e |- (
    K =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA24 J C D E F S )
          `
          ( NTP4VCShift ( NTP4VCA7 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA24 J C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA23 D W B ) x )
          ) =/= 0
          ->
          ( 0 <_ x -> ( x < K -> ( x < S -> ( T ` x ) = 0 ) ) )
        )
      )
  ) $.

  ntp4vc-prefix-idle-before-i4 $e |- (
    K = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA24 J C D E F S )
          `
          ( NTP4VCShift ( NTP4VCA7 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA24 J C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA23 D W B ) x )
          ) =/= 0
          ->
          ( 0 <_ x -> ( x < L -> ( x < S -> ( T ` x ) = 0 ) ) )
        )
      )
  ) $.

  ntp4vc-dual-witness-zero-before-i3 $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA24 J C D E F S )
        ( NTP4VCA19 D E F ) ( NTP4VCA7 D B )
        S ( NTP4VCX5 R L )
    )
    ->
    A. x e. ZZ
      (
        x < A
        ->
        (
          ( NTP4VCX5 R L ) <_ x
          ->
          (
            (
              ( NTP4VCA24 J C D E F S )
              `
              ( NTP4VCShift ( NTP4VCA19 D E F ) x )
            ) = 0
            \/
            (
              ( NTP4VCA24 J C D E F S )
              `
              ( NTP4VCShift ( NTP4VCA7 D B ) x )
            ) = 0
          )
        )
      )
  ) $.

  ntp4vc-i1-to-i4-not-idle-core $e |- (
    K =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA24 J C D E F S )
          `
          ( NTP4VCShift ( NTP4VCA7 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA24 J C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA23 D W B ) x )
          ) =/= 0
          ->
          (
            0 <_ x
            ->
            (
              K <_ x
              ->
              (
                x < L
                ->
                (
                  x < S
                  ->
                  -. (
                    NTP4VCIdleCore
                      D ( NTP4VCA24 J C D E F S ) x S X T
                  )
                )
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-found-or-not-idle-core $e |- (
    K =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA24 J C D E F S )
          `
          ( NTP4VCShift ( NTP4VCA23 D W B ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < S
            ->
            (
              (
                ( NTP4VCA24 J C D E F S )
                `
                ( NTP4VCShift ( NTP4VCA19 D E F ) x )
              ) =/= 0
              \/
              -. (
                NTP4VCIdleCore
                  D ( NTP4VCA24 J C D E F S ) x S X T
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-i2-boolean-range $e |- ( M = 0 \/ M = 1 ) $.

  ntp4vc-a21-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < S
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA21 D B ) S
            ( NTP4VCStorage D ( NTP4VCShift E x ) ) S
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < S
        ->
        (
          ( NTP4VCValidRD N ( NTP4VCShift E x ) 1 )
          /\
          (
            NTP4VCValidRW
              N ( NTP4VCStorage D ( NTP4VCShift E x ) ) S
          )
        )
      )
    ) $.

  ntp4vc-a22-mask-equivalence $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < S
        ->
        (
          (
            ( NTP4VCA22 I C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA23 D W B ) x )
          ) =/= 0
          <->
          (
            ( NTP4VCA22 I C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA19 D E F ) x )
          ) =/= 0
        )
      )
    ) $.

  ntp4vc-a24-a19-to-a23 $e |- A. x e. ZZ
    (
      (
        ( NTP4VCA24 J C D E F S )
        `
        ( NTP4VCShift ( NTP4VCA19 D E F ) x )
      ) =/= 0
      ->
      (
        0 <_ x
        ->
        (
          x < S
          ->
          (
            ( NTP4VCA24 J C D E F S )
            `
            ( NTP4VCShift ( NTP4VCA23 D W B ) x )
          ) =/= 0
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( U ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( U ` x ) ) S )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < S
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( U ` x ) ) S
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) S
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( V ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( V ` x ) ) S )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < S
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( V ` x ) ) S
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) S
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( W ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( W ` x ) ) S )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < S
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( W ` x ) ) S
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) S
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
        x < S
        ->
        (
          ( NTP4VCValidRD N ( X ` x ) 1 )
          /\
          (
            ( NTP4VCValidRD N ( NTP4VCStorage D ( X ` x ) ) S )
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < S
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage D ( X ` x ) ) S
                      ( NTP4VCStorage D ( NTP4VCShift E y ) ) S
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-should-we-balance-loop-inv-preserved-goal11 $a |- (
    ( -u 1 ) <_ A
  ) $.
$}
