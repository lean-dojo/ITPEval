$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_loop_inv_i5_preserved_goal21:
  the should-we-balance verification condition preserves the loop invariant
  that CPU i_5 is not an idle core after the memory havoc update, under the
  generated integer bounds, branch facts, memory validity, framing, linking,
  separation, scan invariants, and quantified scheduler-mask assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. The named operations below explicitly define source shift,
  havoc, read/write validity, separation, framing, and the C integer ranges.
  Every source let-bound address or memory value a_2 through a_27 and x_1
  through x_4 is retained by an explicit definition; source x is the direct
  application of l_idle_cpu to i_6.

  K is the source allocation map t. The arbitrary objects L through T
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

$v swb21p $.
ntp4vc-p-class-variable $f class swb21p $.

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCHavoc
  NTP4VCStorage NTP4VCMaxSint32 NTP4VCMaxIndex NTP4VCSint32Limit
  NTP4VCUint32Limit NTP4VCUint8Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated NTP4VCFramed
  NTP4VCSint32 NTP4VCUint32 NTP4VCUint8 NTP4VCIdleCore
  NTP4VCDualWitness
  NTP4VCA2 NTP4VCX NTP4VCA3 NTP4VCA4 NTP4VCA5 NTP4VCA6
  NTP4VCA7 NTP4VCX1 NTP4VCX2 NTP4VCA8 NTP4VCA9 NTP4VCA10
  NTP4VCA11 NTP4VCA12 NTP4VCA13 NTP4VCA14 NTP4VCA15
  NTP4VCA16 NTP4VCA17 NTP4VCA18 NTP4VCA19 NTP4VCA20
  NTP4VCA21 NTP4VCA22 NTP4VCA23 NTP4VCA24 NTP4VCA25
  NTP4VCA26 NTP4VCA27 NTP4VCX3
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

ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B C ) $.
ntp4vc-a11-class $a class ( NTP4VCA11 A B C ) $.
ntp4vc-a12-class $a class ( NTP4VCA12 A B C D E F ) $.
ntp4vc-a13-class $a class ( NTP4VCA13 A ) $.
ntp4vc-a14-class $a class ( NTP4VCA14 A B ) $.
ntp4vc-a15-class $a class ( NTP4VCA15 A B ) $.
ntp4vc-a16-class $a class ( NTP4VCA16 A B ) $.
ntp4vc-a17-class $a class ( NTP4VCA17 A B C ) $.
ntp4vc-a18-class $a class ( NTP4VCA18 A B C ) $.
ntp4vc-a19-class $a class ( NTP4VCA19 A B ) $.
ntp4vc-a20-class $a class ( NTP4VCA20 A B ) $.
ntp4vc-a21-class $a class ( NTP4VCA21 A B C D E F ) $.
ntp4vc-a22-class $a class ( NTP4VCA22 A B C D E F G ) $.
ntp4vc-a23-class $a class ( NTP4VCA23 A B C D E F G H ) $.
ntp4vc-a24-class $a class ( NTP4VCA24 A B C D E F G H ) $.
ntp4vc-a25-class $a class ( NTP4VCA25 A B C D E F G H I ) $.
ntp4vc-a26-class $a class ( NTP4VCA26 A B C D E F G ) $.
ntp4vc-a27-class $a class ( NTP4VCA27 A B C ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.

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

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 3 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` ( NTP4VCA2 B ) ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 4 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) = ( A ` ( NTP4VCA3 B ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( NTP4VCShift ( NTP4VCA4 A B ) 0 ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B ) = ( A ` ( NTP4VCA5 A B ) ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A ) = ( NTP4VCShift A 1 ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) = ( A ` ( NTP4VCA7 B ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  (
    A
    `
    ( NTP4VCShift ( NTP4VCA6 B C ) ( NTP4VCX1 A C ) )
  ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B ) =
  ( NTP4VCShift ( NTP4VCA8 A B ) 0 ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B C ) =
  ( A ` ( NTP4VCA9 B C ) ) $.
ntp4vc-a11-def $a |- ( NTP4VCA11 A B C ) =
  ( NTP4VCShift ( NTP4VCA10 A B C ) 0 ) $.
ntp4vc-a12-def $a |- ( NTP4VCA12 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA11 C D E ) F ) $.
ntp4vc-a13-def $a |- ( NTP4VCA13 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a14-def $a |- ( NTP4VCA14 A B ) =
  ( A ` ( NTP4VCA13 B ) ) $.
ntp4vc-a15-def $a |- ( NTP4VCA15 A B ) =
  ( NTP4VCShift ( NTP4VCA14 A B ) 0 ) $.
ntp4vc-a16-def $a |- ( NTP4VCA16 A B ) =
  ( A ` ( NTP4VCA15 A B ) ) $.
ntp4vc-a17-def $a |- ( NTP4VCA17 A B C ) =
  ( A ` ( NTP4VCA16 B C ) ) $.
ntp4vc-a18-def $a |- ( NTP4VCA18 A B C ) =
  ( A ` ( NTP4VCShift ( NTP4VCA17 B A C ) 0 ) ) $.
ntp4vc-a19-def $a |- ( NTP4VCA19 A B ) =
  ( NTP4VCShift ( NTP4VCA14 A B ) 1 ) $.
ntp4vc-a20-def $a |- ( NTP4VCA20 A B ) =
  ( NTP4VCShift ( NTP4VCA6 A B ) 0 ) $.
ntp4vc-a21-def $a |- ( NTP4VCA21 A B C D E F ) =
  ( NTP4VCHavoc A B ( NTP4VCA11 C D E ) F ) $.
ntp4vc-a22-def $a |- ( NTP4VCA22 A B C D E F G ) =
  ( ( NTP4VCA12 A B C D E F ) `
    ( NTP4VCShift ( NTP4VCA10 C D E ) G ) ) $.
ntp4vc-a23-def $a |- ( NTP4VCA23 A B C D E F G H ) =
  ( ( NTP4VCA12 A B C D E F ) `
    ( NTP4VCShift ( NTP4VCA6 C G ) H ) ) $.
ntp4vc-a24-def $a |- ( NTP4VCA24 A B C D E F G H ) =
  ( ( NTP4VCA12 A B C D E F ) `
    ( NTP4VCShift ( NTP4VCA6 C G ) H ) ) $.
ntp4vc-a25-def $a |- ( NTP4VCA25 A B C D E F G H I ) =
  ( ( NTP4VCA12 A B C D E F ) `
    ( NTP4VCShift ( NTP4VCA18 C G H ) I ) ) $.
ntp4vc-a26-def $a |- ( NTP4VCA26 A B C D E F G ) =
  ( ( NTP4VCA12 A B C D E F ) ` ( NTP4VCA19 C G ) ) $.
ntp4vc-a27-def $a |- ( NTP4VCA27 A B C ) =
  ( NTP4VCShift ( NTP4VCA18 A B C ) 0 ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) = ( A ` B ) $.

${
  $d x y z w v A B C D E F G H I J K L M N O P Q R S T U V W X Y Z swb21p $.

  $( Source parameters:
     A=i_6, B=a_1, C=t_3, D=t_5, E=a, F=i, G=t_2, H=t_1,
     I=i_1, J=i_7, K=i_3, L=i_4, M=i_5, N=t, O=i_2,
     swb21p=p, and P=t_4. Q is region, R is the extension of
     linked, S is to_uint32, T is l_size, U is l_idle_cpu,
     V is l_sched_group_cpus, W is l_sched_group_mask,
     X is l_group_balance_mask, and Y is l_cpu_smt_mask. $)

  ntp4vc-i6-integer $e |- A e. ZZ $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t3-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t5-pointer-map $e |- D e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-t2-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t1-memory $e |- H e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- I e. ZZ $.
  ntp4vc-i7-integer $e |- J e. ZZ $.
  ntp4vc-i3-integer $e |- K e. ZZ $.
  ntp4vc-i4-integer $e |- L e. ZZ $.
  ntp4vc-i5-integer $e |- M e. ZZ $.
  ntp4vc-allocation-map $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-i2-integer $e |- O e. ZZ $.
  ntp4vc-p-boolean $e |- swb21p e. 2o $.
  ntp4vc-t4-memory $e |- P e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- Q e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- R C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- S e. ( ZZ ^m ZZ ) $.
  ntp4vc-size-integer $e |- T e. ZZ $.
  ntp4vc-idle-cpu-function $e |- U e. ( ZZ ^m ZZ ) $.
  ntp4vc-sched-group-cpus-function
    $e |- V e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-sched-group-mask-function
    $e |- W e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-group-balance-mask-function
    $e |- X e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-cpu-smt-mask-function
    $e |- Y e. ( NTP4VCAddr ^m ZZ ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NTP4VCAddr )
      A. z e. ( NTP4VCAddr ^m NTP4VCAddr )
        (
          0 <_ x
          ->
          (
            x < T
            ->
            (
              y `
              ( NTP4VCShift ( z ` ( NTP4VCShift ( Y ` x ) 0 ) ) x )
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
              ( NTP4VCShift ( w ` ( NTP4VCShift ( Y ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < T
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < T
                    ->
                    (
                      z `
                      ( NTP4VCShift
                        ( w ` ( NTP4VCShift ( Y ` x ) 0 ) ) y )
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
                  ( w ` ( NTP4VCShift ( Y ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NTP4VCShift
                    ( w ` ( NTP4VCShift ( Y ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < T
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < T
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < T
                            ->
                            (
                              z `
                              ( NTP4VCShift
                                ( w ` ( NTP4VCShift ( Y ` x ) 0 ) ) v )
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
    ( NTP4VCUint32 ( S ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( S ` x ) = x ) $.
  ntp4vc-size-properties $e |- ( 0 < T /\ T <_ NTP4VCMaxSint32 ) $.
  ntp4vc-idle-cpu-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( U ` x ) ) $.

  ntp4vc-i3-not-minus-one $e |- K =/= ( -u 1 ) $.
  ntp4vc-idle-i6-iff-i4-nonzero $e |- (
    ( ( U ` A ) =/= 0 ) <-> ( L =/= 0 )
  ) $.
  ntp4vc-x1-not-two $e |- ( NTP4VCX C B ) =/= 2 $.
  ntp4vc-x3-nonzero $e |- ( NTP4VCX2 C D B ) =/= 0 $.
  ntp4vc-a12-a6-i5-nonzero $e |- (
    ( ( NTP4VCA12 G C D E F T ) `
      ( NTP4VCShift ( NTP4VCA6 D B ) M ) ) =/= 0
  ) $.
  ntp4vc-a12-a18-i5-nonzero $e |- (
    ( ( NTP4VCA12 G C D E F T ) `
      ( NTP4VCShift ( NTP4VCA18 D X B ) M ) ) =/= 0
  ) $.
  ntp4vc-i-nonnegative $e |- 0 <_ F $.
  ntp4vc-i-lt-size $e |- F < T $.
  ntp4vc-i5-nonnegative $e |- 0 <_ M $.
  ntp4vc-i3-le-i5 $e |- K <_ M $.
  ntp4vc-i5-lt-size $e |- M < T $.
  ntp4vc-i6-nonnegative $e |- 0 <_ A $.
  ntp4vc-i5-le-i6 $e |- M <_ A $.
  ntp4vc-i6-lt-size $e |- A < T $.
  ntp4vc-i7-nonnegative $e |- 0 <_ J $.
  ntp4vc-i7-le-size $e |- J <_ T $.
  ntp4vc-converted-i6-lt-size $e |- ( S ` A ) < T $.
  ntp4vc-x2-nonnegative $e |- 0 <_ ( NTP4VCX1 C B ) $.
  ntp4vc-x2-lt-size $e |- ( NTP4VCX1 C B ) < T $.
  ntp4vc-region-a $e |- ( Q ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( Q ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed Q D ) $.
  ntp4vc-linked-allocation $e |- N e. R $.
  ntp4vc-i4-uint8 $e |- ( NTP4VCUint8 L ) $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 I ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 O ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 K ) $.
  ntp4vc-i6-sint32 $e |- ( NTP4VCSint32 A ) $.
  ntp4vc-i7-sint32 $e |- ( NTP4VCSint32 J ) $.
  ntp4vc-a1-valid-rd $e |- ( NTP4VCValidRD N B 5 ) $.
  ntp4vc-x1-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX C B ) ) $.
  ntp4vc-i6-successor-sint32 $e |- ( NTP4VCSint32 ( 1 + A ) ) $.
  ntp4vc-x2-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX1 C B ) ) $.
  ntp4vc-a3-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA3 B ) 1 ) $.
  ntp4vc-a7-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA7 B ) 1 ) $.
  ntp4vc-a2-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA2 B ) 1 ) $.
  ntp4vc-a13-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA13 B ) 1 ) $.
  ntp4vc-a8-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA8 E F ) 1 ) $.
  ntp4vc-a4-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA4 D B ) 1 ) $.
  ntp4vc-a1-field-valid-rd $e |- (
    NTP4VCValidRD N ( D ` ( NTP4VCShift B 2 ) ) 2
  ) $.
  ntp4vc-a14-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA14 D B ) 2 ) $.
  ntp4vc-a19-value-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCA19 D B ) )
  ) $.
  ntp4vc-a9-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA9 E F ) 1 ) $.
  ntp4vc-a5-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA5 D B ) 1 ) $.
  ntp4vc-a15-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA15 D B ) 1 ) $.
  ntp4vc-a16-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA16 D B ) 1 ) $.
  ntp4vc-a17-valid-rd $e |- ( NTP4VCValidRD N ( NTP4VCA17 X D B ) 1 ) $.
  ntp4vc-x3-uint8 $e |- ( NTP4VCUint8 ( NTP4VCX2 C D B ) ) $.
  ntp4vc-a11-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA11 D E F ) T
  ) $.
  ntp4vc-a20-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA20 D B ) T
  ) $.
  ntp4vc-a11-valid-rw $e |- (
    NTP4VCValidRW N ( NTP4VCA11 D E F ) T
  ) $.

  ntp4vc-a21-a6-minus-one-uint8 $e |- (
    NTP4VCUint8
      ( ( NTP4VCA21 H C D E F T ) `
        ( NTP4VCShift ( NTP4VCA6 D B ) ( -u 1 ) ) )
  ) $.
  ntp4vc-a21-a18-minus-one-uint8 $e |- (
    NTP4VCUint8
      ( ( NTP4VCA21 H C D E F T ) `
        ( NTP4VCShift ( NTP4VCA18 D X B ) ( -u 1 ) ) )
  ) $.
  ntp4vc-a22-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA22 G C D E F T A )
  ) $.
  ntp4vc-a23-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA23 G C D E F T B I )
  ) $.
  ntp4vc-a12-a6-i3-uint8 $e |- (
    NTP4VCUint8
      ( ( NTP4VCA12 G C D E F T ) `
        ( NTP4VCShift ( NTP4VCA6 D B ) K ) )
  ) $.
  ntp4vc-a24-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA24 G C D E F T B A )
  ) $.
  ntp4vc-a25-uint8 $e |- (
    NTP4VCUint8 ( NTP4VCA25 G C D E F T X B I )
  ) $.
  ntp4vc-a12-a18-i3-uint8 $e |- (
    NTP4VCUint8
      ( ( NTP4VCA12 G C D E F T ) `
        ( NTP4VCShift ( NTP4VCA18 D X B ) K ) )
  ) $.
  ntp4vc-a21-a19-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCA21 H C D E F T ) ` ( NTP4VCA19 D B ) )
  ) $.
  ntp4vc-a26-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA26 G C D E F T B )
  ) $.
  ntp4vc-a27-valid-rd $e |- (
    NTP4VCValidRD N ( NTP4VCA27 D X B ) T
  ) $.
  ntp4vc-a11-a27-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCA11 D E F ) T ( NTP4VCA27 D X B ) T
  ) $.

  ntp4vc-source-branch $e |- (
    (
      L = 0
      ->
      ( K = I /\ A <_ NTP4VCMaxIndex )
    )
    /\
    (
      L =/= 0
      ->
      (
        swb21p = 0
        /\
        (
          O = I
          /\
          (
            ( U ` A ) =/= 0
            /\
            (
              ( ( P ` ( NTP4VCA19 D B ) ) mod 8 ) = 0
              /\
              (
                ( NTP4VCA12 G C D E F T ) = P
                /\
                (
                  A <_ NTP4VCMaxIndex
                  /\
                  (
                    -. ( NTP4VCIdleCore D P A T Y U )
                    /\
                    (
                      ( NTP4VCValidRD N ( NTP4VCA19 D B ) 1 )
                      /\
                      (
                        ( O = ( -u 1 ) -> A = K )
                        /\
                        ( O =/= ( -u 1 ) -> K = O )
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

  ntp4vc-land-branch $e |- (
    ( ( NTP4VCA26 G C D E F T B ) mod 8 ) =/= 0
    -> I = ( -u 1 )
  ) $.

  ntp4vc-i1-found-properties $e |- (
    I =/= ( -u 1 )
    ->
    (
      ( U ` I ) =/= 0
      /\
      (
        ( NTP4VCA23 G C D E F T B I ) =/= 0
        /\
        (
          ( NTP4VCA25 G C D E F T X B I ) =/= 0
          /\
          ( 0 <_ I /\ I < T )
        )
      )
    )
  ) $.

  ntp4vc-no-i1-transfers-mask $e |- (
    I = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA12 G C D E F T ) `
          ( NTP4VCShift ( NTP4VCA18 D X B ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < T
            ->
            (
              ( NTP4VCA12 G C D E F T ) `
              ( NTP4VCShift ( NTP4VCA10 D E F ) x )
            ) =/= 0
          )
        )
      )
  ) $.

  ntp4vc-dual-witness-lower-bound $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA12 G C D E F T )
        ( NTP4VCA10 D E F ) ( NTP4VCA6 D B )
        T ( NTP4VCX3 S J )
    )
    -> ( NTP4VCX3 S J ) <_ A
  ) $.
  ntp4vc-dual-witness-selected-nonzero $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA12 G C D E F T )
        ( NTP4VCA10 D E F ) ( NTP4VCA6 D B )
        T ( NTP4VCX3 S J )
    )
    ->
    (
      ( NTP4VCA22 G C D E F T A ) =/= 0
      /\
      ( NTP4VCA24 G C D E F T B A ) =/= 0
    )
  ) $.

  ntp4vc-all-tail-zero-implies-i6-is-size $e |- (
    (
      A. x e. ZZ
        (
          x < T
          ->
          (
            ( NTP4VCX3 S J ) <_ x
            ->
            (
              (
                ( NTP4VCA12 G C D E F T ) `
                ( NTP4VCShift ( NTP4VCA10 D E F ) x )
              ) = 0
              \/
              (
                ( NTP4VCA12 G C D E F T ) `
                ( NTP4VCShift ( NTP4VCA6 D B ) x )
              ) = 0
            )
          )
        )
    )
    -> T = A
  ) $.

  ntp4vc-prefix-idle-before-i1 $e |- (
    I =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA12 G C D E F T ) `
          ( NTP4VCShift ( NTP4VCA6 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA12 G C D E F T ) `
            ( NTP4VCShift ( NTP4VCA18 D X B ) x )
          ) =/= 0
          ->
          (
            0 <_ x
            -> ( x < I -> ( x < T -> ( U ` x ) = 0 ) )
          )
        )
      )
  ) $.

  ntp4vc-prefix-idle-before-i7 $e |- (
    I = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA12 G C D E F T ) `
          ( NTP4VCShift ( NTP4VCA6 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA12 G C D E F T ) `
            ( NTP4VCShift ( NTP4VCA18 D X B ) x )
          ) =/= 0
          ->
          (
            0 <_ x
            -> ( x < J -> ( x < T -> ( U ` x ) = 0 ) )
          )
        )
      )
  ) $.

  ntp4vc-dual-witness-zero-before-i6 $e |- (
    (
      NTP4VCDualWitness
        ( NTP4VCA12 G C D E F T )
        ( NTP4VCA10 D E F ) ( NTP4VCA6 D B )
        T ( NTP4VCX3 S J )
    )
    ->
    A. x e. ZZ
      (
        x < A
        ->
        (
          ( NTP4VCX3 S J ) <_ x
          ->
          (
            (
              ( NTP4VCA12 G C D E F T ) `
              ( NTP4VCShift ( NTP4VCA10 D E F ) x )
            ) = 0
            \/
            (
              ( NTP4VCA12 G C D E F T ) `
              ( NTP4VCShift ( NTP4VCA6 D B ) x )
            ) = 0
          )
        )
      )
  ) $.

  ntp4vc-i1-to-i7-not-idle-core $e |- (
    I =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA12 G C D E F T ) `
          ( NTP4VCShift ( NTP4VCA6 D B ) x )
        ) =/= 0
        ->
        (
          (
            ( NTP4VCA12 G C D E F T ) `
            ( NTP4VCShift ( NTP4VCA18 D X B ) x )
          ) =/= 0
          ->
          (
            0 <_ x
            ->
            (
              I <_ x
              ->
              (
                x < J
                ->
                (
                  x < T
                  ->
                  -. (
                    NTP4VCIdleCore
                      D ( NTP4VCA12 G C D E F T ) x T Y U
                  )
                )
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-found-or-not-idle-core $e |- (
    I =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NTP4VCA12 G C D E F T ) `
          ( NTP4VCShift ( NTP4VCA18 D X B ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < T
            ->
            (
              (
                ( NTP4VCA12 G C D E F T ) `
                ( NTP4VCShift ( NTP4VCA10 D E F ) x )
              ) =/= 0
              \/
              -. (
                NTP4VCIdleCore
                  D ( NTP4VCA12 G C D E F T ) x T Y U
              )
            )
          )
        )
      )
  ) $.

  ntp4vc-i4-boolean-range $e |- ( L = 0 \/ L = 1 ) $.

  ntp4vc-a20-separated-from-cpu-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < T
        ->
        (
          NTP4VCSeparated
            ( NTP4VCA20 D B ) T
            ( NTP4VCStorage D ( NTP4VCShift E x ) ) T
        )
      )
    ) $.

  ntp4vc-cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < T
        ->
        (
          ( NTP4VCValidRD N ( NTP4VCShift E x ) 1 )
          /\
          (
            NTP4VCValidRW
              N ( NTP4VCStorage D ( NTP4VCShift E x ) ) T
          )
        )
      )
    ) $.

  ntp4vc-a21-mask-equivalence $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < T
        ->
        (
          (
            ( NTP4VCA21 H C D E F T ) `
            ( NTP4VCShift ( NTP4VCA18 D X B ) x )
          ) =/= 0
          <->
          (
            ( NTP4VCA21 H C D E F T ) `
            ( NTP4VCShift ( NTP4VCA10 D E F ) x )
          ) =/= 0
        )
      )
    ) $.

  ntp4vc-a12-a10-to-a18 $e |- A. x e. ZZ
    (
      (
        ( NTP4VCA12 G C D E F T ) `
        ( NTP4VCShift ( NTP4VCA10 D E F ) x )
      ) =/= 0
      ->
      (
        0 <_ x
        ->
        (
          x < T
          ->
          (
            ( NTP4VCA12 G C D E F T ) `
            ( NTP4VCShift ( NTP4VCA18 D X B ) x )
          ) =/= 0
        )
      )
    ) $.

  ntp4vc-sched-group-cpus-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( V ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( V ` x ) ) T )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < T
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( V ` x ) ) T
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) T
              )
            )
          )
      )
    ) $.

  ntp4vc-sched-group-mask-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( W ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( W ` x ) ) T )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < T
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( W ` x ) ) T
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) T
              )
            )
          )
      )
    ) $.

  ntp4vc-group-balance-mask-validity $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCValidRD N ( X ` x ) 1 )
      /\
      (
        ( NTP4VCValidRD N ( NTP4VCStorage D ( X ` x ) ) T )
        /\
        A. y e. ZZ
          (
            0 <_ y
            ->
            (
              y < T
              ->
              (
                NTP4VCSeparated
                  ( NTP4VCStorage D ( X ` x ) ) T
                  ( NTP4VCStorage D ( NTP4VCShift E y ) ) T
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
        x < T
        ->
        (
          ( NTP4VCValidRD N ( Y ` x ) 1 )
          /\
          (
            ( NTP4VCValidRD N ( NTP4VCStorage D ( Y ` x ) ) T )
            /\
            A. y e. ZZ
              (
                0 <_ y
                ->
                (
                  y < T
                  ->
                  (
                    NTP4VCSeparated
                      ( NTP4VCStorage D ( Y ` x ) ) T
                      ( NTP4VCStorage D ( NTP4VCShift E y ) ) T
                  )
                )
              )
          )
        )
      )
    ) $.

  ntp4vc-should-we-balance-loop-inv-i5-preserved-goal21 $a |- (
    -. (
      NTP4VCIdleCore
        D ( NTP4VCA12 G C D E F T ) M T Y U
    )
  ) $.
$}
