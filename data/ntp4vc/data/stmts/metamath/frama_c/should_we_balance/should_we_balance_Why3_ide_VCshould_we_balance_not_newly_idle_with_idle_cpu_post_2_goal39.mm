$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/should_we_balance/should_we_balance_Why3_ide_VCshould_we_balance_not_newly_idle_with_idle_cpu_post_2_goal39:
  the should-we-balance verification condition equates selection of CPU i_6
  with a nonzero Boolean result after the modeled CPU-mask search, under the
  generated integer bounds, memory validity, havoc, separation, framing,
  idle-core, scan, and scheduler-mask assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Integers are the full set ZZ and addresses are exactly ZZ X. ZZ.  The
  definitions below faithfully expand source shift, havoc, read/write
  validity, separation, framing, integer-width predicates, p_idle_core, every
  source let binding, the repeated existential scan condition, and the
  quantified scheduler-mask contexts.  Bitwise land 7 z is represented by
  z mod 8, its exact value on mathematical integers.

  Source parameters remain arbitrary objects of their full function and
  integer domains.  The source curried implication chain is split into scoped
  essential hypotheses, which is bidirectionally equivalent to the original
  proposition.  Existential witnesses remain internal and every quantified
  integer and address retains its full domain.  The final declaration is
  Metamath's native unproved $a statement encoding; there is no $p proof
  declaration in this file.
$)

$v
  g39a1 g39t7 g39t8 g39a g39i g39t6 g39i8 g39i3 g39i9 g39t5 g39i5 g39i6 g39tm g39i1 g39i2 g39i4 g39i7 g39i10
  g39t4 g39t1 g39t2 g39t3 g39region g39linked g39to_uint32 g39size g39idle g39sgcpus g39sgmask
  g39gbmask g39gbcpu g39smtmask
$.

a1c $f class g39a1 $.
t7c $f class g39t7 $.
t8c $f class g39t8 $.
ac $f class g39a $.
ic $f class g39i $.
t6c $f class g39t6 $.
i8c $f class g39i8 $.
i3c $f class g39i3 $.
i9c $f class g39i9 $.
t5c $f class g39t5 $.
i5c $f class g39i5 $.
i6c $f class g39i6 $.
tmc $f class g39tm $.
i1c $f class g39i1 $.
i2c $f class g39i2 $.
i4c $f class g39i4 $.
i7c $f class g39i7 $.
i10c $f class g39i10 $.
t4c $f class g39t4 $.
t1c $f class g39t1 $.
t2c $f class g39t2 $.
t3c $f class g39t3 $.
regionc $f class g39region $.
linkedc $f class g39linked $.
to_uint32c $f class g39to_uint32 $.
sizec $f class g39size $.
idlec $f class g39idle $.
sgcpusc $f class g39sgcpus $.
sgmaskc $f class g39sgmask $.
gbmaskc $f class g39gbmask $.
gbcpuc $f class g39gbcpu $.
smtmaskc $f class g39smtmask $.

$c
  NAddr NBase NOffset NShift NHavoc NStorage
  NSint32Limit NUint32Limit NUint8Limit NMaxSint32
  NValidRD NValidRW NSeparated NFramed NSint32 NUint32 NUint8
  NIdleCore NDualWitness NMaskContext
  NA2 NX NA3 NA4 NA5 NX1 NA6 NA7 NA8 NA9 NA10 NX2 NX3
  NA11 NA12 NA13 NA14 NA15 NA16 NA17 NA18 NA19 NA20
  NA21 NA22 NA23 NA24 NA25 NA26 NA27 NX4 NX5 NA28
$.

naddr-class $a class NAddr $.
nbase-class $a class ( NBase A ) $.
noffset-class $a class ( NOffset A ) $.
nshift-class $a class ( NShift A B ) $.
nhavoc-class $a class ( NHavoc A B C D ) $.
nstorage-class $a class ( NStorage A B ) $.
nsint32limit-class $a class NSint32Limit $.
nuint32limit-class $a class NUint32Limit $.
nuint8limit-class $a class NUint8Limit $.
nmaxsint32-class $a class NMaxSint32 $.

nvalidrd-syntax $a wff ( NValidRD A B C ) $.
nvalidrw-syntax $a wff ( NValidRW A B C ) $.
nseparated-syntax $a wff ( NSeparated A B C D ) $.
nframed-syntax $a wff ( NFramed A B ) $.
nsint32-syntax $a wff ( NSint32 A ) $.
nuint32-syntax $a wff ( NUint32 A ) $.
nuint8-syntax $a wff ( NUint8 A ) $.
nidlecore-syntax $a wff ( NIdleCore A B C D E F ) $.
ndualwitness-syntax $a wff ( NDualWitness A B C D E ) $.
nmaskcontext-syntax
  $a wff ( NMaskContext A B C D E F G H I ) $.

na2-class $a class ( NA2 A ) $.
nx-class $a class ( NX A B ) $.
na3-class $a class ( NA3 A ) $.
na4-class $a class ( NA4 A B ) $.
na5-class $a class ( NA5 A B ) $.
nx1-class $a class ( NX1 A B C ) $.
na6-class $a class ( NA6 A ) $.
na7-class $a class ( NA7 A B ) $.
na8-class $a class ( NA8 A B ) $.
na9-class $a class ( NA9 A B ) $.
na10-class $a class ( NA10 A ) $.
nx2-class $a class ( NX2 A B ) $.
nx3-class $a class ( NX3 A B C ) $.
na11-class $a class ( NA11 A B ) $.
na12-class $a class ( NA12 A B ) $.
na13-class $a class ( NA13 A B C ) $.
na14-class $a class ( NA14 A B C D ) $.
na15-class $a class ( NA15 A B ) $.
na16-class $a class ( NA16 A B ) $.
na17-class $a class ( NA17 A B C ) $.
na18-class $a class ( NA18 A B C ) $.
na19-class $a class ( NA19 A B ) $.
na20-class $a class ( NA20 A B C D E F ) $.
na21-class $a class ( NA21 A B C D E F G H ) $.
na22-class $a class ( NA22 A B C D E F G H I ) $.
na23-class $a class ( NA23 A B C D E F G H I ) $.
na24-class $a class ( NA24 A B C D E F G H I J ) $.
na25-class $a class ( NA25 A B C D E F G ) $.
na26-class $a class ( NA26 A B C D ) $.
na27-class $a class ( NA27 A B C D E F G ) $.
nx4-class $a class ( NX4 A B C D E F G ) $.
nx5-class $a class ( NX5 A B ) $.
na28-class $a class ( NA28 A B C D E F ) $.

naddr-def $a |- NAddr = ( ZZ X. ZZ ) $.
nbase-def $a |- ( NBase A ) = ( 1st ` A ) $.
noffset-def $a |- ( NOffset A ) = ( 2nd ` A ) $.
nshift-def $a |- ( NShift A B ) =
  <. ( NBase A ) , ( ( NOffset A ) + B ) >. $.

nsint32limit-def $a |- NSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
nuint32limit-def $a |- NUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
nuint8limit-def $a |- NUint8Limit = ; ; 2 5 6 $.
nmaxsint32-def $a |- NMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.

nvalidrd-def $a |- ( ( NValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NBase B ) =/= 0
      /\
      (
        0 <_ ( NOffset B )
        /\
        ( ( NOffset B ) + C ) <_ ( A ` ( NBase B ) )
      )
    )
  )
) $.

nvalidrw-def $a |- ( ( NValidRW A B C ) <->
  (
    0 < C
    ->
    (
      0 < ( NBase B )
      /\
      (
        0 <_ ( NOffset B )
        /\
        ( ( NOffset B ) + C ) <_ ( A ` ( NBase B ) )
      )
    )
  )
) $.

nseparated-def $a |- ( ( NSeparated A B C D ) <->
  (
    B <_ 0
    \/
    (
      D <_ 0
      \/
      (
        ( NBase A ) =/= ( NBase C )
        \/
        (
          ( ( NOffset C ) + D ) <_ ( NOffset A )
          \/
          ( ( NOffset A ) + B ) <_ ( NOffset C )
        )
      )
    )
  )
) $.

${
  $d x A B C D $.
  nhavoc-def $a |- ( NHavoc A B C D ) =
    (
      x e. NAddr |->
        if ( ( NSeparated x 1 C D ) , ( B ` x ) , ( A ` x ) )
    ) $.
$}

nstorage-def $a |- ( NStorage A B ) =
  ( NShift ( A ` ( NShift B 0 ) ) 0 ) $.

${
  $d x A B $.
  nframed-def $a |- ( ( NFramed A B ) <->
    A. x e. NAddr ( ( A ` ( NBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

nsint32-def $a |- ( ( NSint32 A ) <->
  ( -u NSint32Limit <_ A /\ A < NSint32Limit )
) $.
nuint32-def $a |- ( ( NUint32 A ) <->
  ( 0 <_ A /\ A < NUint32Limit )
) $.
nuint8-def $a |- ( ( NUint8 A ) <->
  ( 0 <_ A /\ A < NUint8Limit )
) $.

${
  $d x A B C D E F $.
  nidlecore-def $a |- ( ( NIdleCore A B C D E F ) <->
    A. x e. ZZ
      (
        ( B ` ( NShift ( A ` ( NShift ( E ` C ) 0 ) ) x ) ) =/= 0
        ->
        ( 0 <_ x -> ( x < D -> ( F ` x ) =/= 0 ) )
      )
  ) $.
$}

${
  $d x A B C D E $.
  ndualwitness-def $a |- ( ( NDualWitness A B C D E ) <->
    E. x e. ZZ
      (
        ( ( A ` ( NShift B x ) ) =/= 0 )
        /\
        (
          ( A ` ( NShift C x ) ) =/= 0
          /\ ( x < D /\ E <_ x )
        )
      )
  ) $.
$}

${
  $d x y A B C D E F G H I $.
  nmaskcontext-def $a |- (
    ( NMaskContext A B C D E F G H I )
    <->
    (
      A. x e. ZZ
        (
          0 <_ x
          ->
          (
            x < D
            ->
            (
              ( NValidRD A ( NShift C x ) 1 )
              /\
              ( NValidRW A ( NStorage B ( NShift C x ) ) D )
            )
          )
        )
      /\
      (
        A. x e. NAddr
          (
            ( NValidRD A ( E ` x ) 1 )
            /\
            (
              ( NValidRD A ( NStorage B ( E ` x ) ) D )
              /\
              A. y e. ZZ
                (
                  0 <_ y
                  ->
                  (
                    y < D
                    ->
                    (
                      NSeparated
                        ( NStorage B ( E ` x ) ) D
                        ( NStorage B ( NShift C y ) ) D
                    )
                  )
                )
            )
          )
        /\
        (
          A. x e. NAddr
            (
              ( NValidRD A ( F ` x ) 1 )
              /\
              (
                ( NValidRD A ( NStorage B ( F ` x ) ) D )
                /\
                A. y e. ZZ
                  (
                    0 <_ y
                    ->
                    (
                      y < D
                      ->
                      (
                        NSeparated
                          ( NStorage B ( F ` x ) ) D
                          ( NStorage B ( NShift C y ) ) D
                      )
                    )
                  )
              )
            )
          /\
          (
            A. x e. NAddr
              (
                ( NValidRD A ( G ` x ) 1 )
                /\
                (
                  ( NValidRD A ( NStorage B ( G ` x ) ) D )
                  /\
                  A. y e. ZZ
                    (
                      0 <_ y
                      ->
                      (
                        y < D
                        ->
                        (
                          NSeparated
                            ( NStorage B ( G ` x ) ) D
                            ( NStorage B ( NShift C y ) ) D
                        )
                      )
                    )
                )
              )
            /\
            A. x e. ZZ
              (
                0 <_ x
                ->
                (
                  x < D
                  ->
                  (
                    ( NValidRD A ( H ` x ) 1 )
                    /\
                    (
                      ( NValidRD A ( NStorage B ( H ` x ) ) D )
                      /\
                      A. y e. ZZ
                        (
                          0 <_ y
                          ->
                          (
                            y < D
                            ->
                            (
                              NSeparated
                                ( NStorage B ( H ` x ) ) D
                                ( NStorage B ( NShift C y ) ) D
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

na2-def $a |- ( NA2 A ) = ( NShift A 3 ) $.
nx-def $a |- ( NX A B ) = ( A ` ( NA2 B ) ) $.
na3-def $a |- ( NA3 A ) = ( NShift A 0 ) $.
na4-def $a |- ( NA4 A B ) = ( A ` ( NA3 B ) ) $.
na5-def $a |- ( NA5 A B ) = ( NShift ( NA4 A B ) 1 ) $.
nx1-def $a |- ( NX1 A B C ) = ( A ` ( NA5 B C ) ) $.
na6-def $a |- ( NA6 A ) = ( NShift A 4 ) $.
na7-def $a |- ( NA7 A B ) = ( A ` ( NA6 B ) ) $.
na8-def $a |- ( NA8 A B ) = ( NShift ( NA7 A B ) 0 ) $.
na9-def $a |- ( NA9 A B ) = ( A ` ( NA8 A B ) ) $.
na10-def $a |- ( NA10 A ) = ( NShift A 1 ) $.
nx2-def $a |- ( NX2 A B ) = ( A ` ( NA10 B ) ) $.
nx3-def $a |- ( NX3 A B C ) =
  ( A ` ( NShift ( NA9 B C ) ( NX2 A C ) ) ) $.
na11-def $a |- ( NA11 A B ) = ( NShift ( NA4 A B ) 0 ) $.
na12-def $a |- ( NA12 A B ) = ( A ` ( NA11 A B ) ) $.
na13-def $a |- ( NA13 A B C ) = ( A ` ( NA12 B C ) ) $.
na14-def $a |- ( NA14 A B C D ) =
  ( A ` ( NShift ( NA13 B C D ) 0 ) ) $.
na15-def $a |- ( NA15 A B ) = ( NShift A B ) $.
na16-def $a |- ( NA16 A B ) = ( NShift ( NA15 A B ) 0 ) $.
na17-def $a |- ( NA17 A B C ) = ( A ` ( NA16 B C ) ) $.
na18-def $a |- ( NA18 A B C ) = ( NShift ( NA17 A B C ) 0 ) $.
na19-def $a |- ( NA19 A B ) = ( NShift ( NA9 A B ) 0 ) $.
na20-def $a |- ( NA20 A B C D E F ) =
  ( NHavoc A B ( NA18 C D E ) F ) $.
na21-def $a |- ( NA21 A B C D E F G H ) =
  ( ( NA20 A B C D E F ) ` ( NShift ( NA17 C D E ) G ) ) $.
na22-def $a |- ( NA22 A B C D E F G H I ) =
  ( ( NA20 A B C D E F ) ` ( NShift ( NA9 C H ) G ) ) $.
na23-def $a |- ( NA23 A B C D E F G H I ) =
  ( ( NA20 A B C D E F ) ` ( NShift ( NA9 C H ) I ) ) $.
na24-def $a |- ( NA24 A B C D E F G H I J ) =
  (
    ( NA20 A B C D E F )
    ` ( NShift ( NA14 C J C H ) I )
  ) $.
na25-def $a |- ( NA25 A B C D E F G ) =
  ( ( NA20 A B C D E F ) ` ( NA5 C G ) ) $.
na26-def $a |- ( NA26 A B C D ) =
  ( NShift ( NA14 A B C D ) 0 ) $.
na27-def $a |- ( NA27 A B C D E F G ) =
  ( ( NA20 A B C D E F ) ` ( NA10 G ) ) $.
nx4-def $a |- ( NX4 A B C D E F G ) =
  ( ( NA25 A B C D E F G ) mod 8 ) $.
nx5-def $a |- ( NX5 A B ) = ( A ` B ) $.
na28-def $a |- ( NA28 A B C D E F ) =
  ( NHavoc A B ( NA18 C D E ) F ) $.

${
  $d
    x y z w v g39a1 g39t7 g39t8 g39a g39i g39t6 g39i8 g39i3 g39i9 g39t5 g39i5 g39i6 g39tm g39i1 g39i2 g39i4 g39i7 g39i10
    g39t4 g39t1 g39t2 g39t3 g39region g39linked g39to_uint32 g39size g39idle g39sgcpus g39sgmask
    g39gbmask g39gbcpu g39smtmask
  $.

  g39a1-address $e |- g39a1 e. NAddr $.
  g39t7-memory $e |- g39t7 e. ( ZZ ^m NAddr ) $.
  g39t8-pointer-map $e |- g39t8 e. ( NAddr ^m NAddr ) $.
  g39a-address $e |- g39a e. NAddr $.
  g39i-integer $e |- g39i e. ZZ $.
  g39t6-memory $e |- g39t6 e. ( ZZ ^m NAddr ) $.
  g39i8-integer $e |- g39i8 e. ZZ $.
  g39i3-integer $e |- g39i3 e. ZZ $.
  g39i9-integer $e |- g39i9 e. ZZ $.
  g39t5-memory $e |- g39t5 e. ( ZZ ^m NAddr ) $.
  g39i5-integer $e |- g39i5 e. ZZ $.
  g39i6-integer $e |- g39i6 e. ZZ $.
  g39tm-allocation $e |- g39tm e. ( ZZ ^m ZZ ) $.
  g39i1-integer $e |- g39i1 e. ZZ $.
  g39i2-integer $e |- g39i2 e. ZZ $.
  g39i4-integer $e |- g39i4 e. ZZ $.
  g39i7-integer $e |- g39i7 e. ZZ $.
  g39i10-integer $e |- g39i10 e. ZZ $.
  g39t4-allocation $e |- g39t4 e. ( ZZ ^m ZZ ) $.
  g39t1-allocation $e |- g39t1 e. ( ZZ ^m ZZ ) $.
  g39t2-allocation $e |- g39t2 e. ( ZZ ^m ZZ ) $.
  g39t3-allocation $e |- g39t3 e. ( ZZ ^m ZZ ) $.
  g39region-function $e |- g39region e. ( ZZ ^m ZZ ) $.
  g39linked-predicate $e |- g39linked C_ ( ZZ ^m ZZ ) $.
  to-uint32-function $e |- g39to_uint32 e. ( ZZ ^m ZZ ) $.
  g39size-integer $e |- g39size e. ZZ $.
  g39idle-function $e |- g39idle e. ( ZZ ^m ZZ ) $.
  g39sgcpus-function $e |- g39sgcpus e. ( NAddr ^m NAddr ) $.
  g39sgmask-function $e |- g39sgmask e. ( NAddr ^m NAddr ) $.
  g39gbmask-function $e |- g39gbmask e. ( NAddr ^m NAddr ) $.
  g39gbcpu-function $e |- g39gbcpu e. ( ZZ ^m NAddr ) $.
  g39smtmask-function $e |- g39smtmask e. ( NAddr ^m ZZ ) $.

  itpeval-q-mask-refl $e |- A. x e. ZZ
    A. y e. ( ZZ ^m NAddr )
      A. z e. ( NAddr ^m NAddr )
        (
          0 <_ x
          ->
          (
            x < g39size
            ->
            (
              y `
              ( NShift ( z ` ( NShift ( g39smtmask ` x ) 0 ) ) x )
            ) =/= 0
          )
        ) $.

  itpeval-q-mask-symm $e |- A. z e. ( ZZ ^m NAddr )
    A. w e. ( NAddr ^m NAddr )
      A. y e. ZZ
        A. x e. ZZ
          (
            (
              z `
              ( NShift ( w ` ( NShift ( g39smtmask ` y ) 0 ) ) x )
            ) =/= 0
            ->
            (
              0 <_ x
              ->
              (
                x < g39size
                ->
                (
                  0 <_ y
                  ->
                  (
                    y < g39size
                    ->
                    (
                      z `
                      ( NShift
                        ( w ` ( NShift ( g39smtmask ` x ) 0 ) ) y )
                    ) =/= 0
                  )
                )
              )
            )
          ) $.

  itpeval-q-mask-trans $e |- A. w e. ( NAddr ^m NAddr )
    A. x e. ZZ
      A. z e. ( ZZ ^m NAddr )
        A. y e. ZZ
          A. v e. ZZ
            (
              (
                z `
                ( NShift
                  ( w ` ( NShift ( g39smtmask ` x ) 0 ) ) y )
              ) =/= 0
              ->
              (
                (
                  z `
                  ( NShift
                    ( w ` ( NShift ( g39smtmask ` y ) 0 ) ) v )
                ) =/= 0
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < g39size
                    ->
                    (
                      0 <_ y
                      ->
                      (
                        y < g39size
                        ->
                        (
                          0 <_ v
                          ->
                          (
                            v < g39size
                            ->
                            (
                              z `
                              ( NShift
                                ( w ` ( NShift ( g39smtmask ` x ) 0 ) ) v )
                            ) =/= 0
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) $.


  to-uint32-range $e |- A. x e. ZZ ( NUint32 ( g39to_uint32 ` x ) ) $.
  to-uint32-identity $e |- A. x e. ZZ
    ( ( NUint32 x ) -> ( g39to_uint32 ` x ) = x ) $.
  g39size-properties $e |- ( 0 < g39size /\ g39size <_ NMaxSint32 ) $.
  g39idle-range $e |- A. x e. ZZ ( NUint8 ( g39idle ` x ) ) $.

  g39idle-g39i5-nonzero $e |- ( g39idle ` g39i5 ) =/= 0 $.
  g39idle-g39i6-nonzero $e |- ( g39idle ` g39i6 ) =/= 0 $.
  x-not-two $e |- ( NX g39t7 g39a1 ) =/= 2 $.
  land-x1-zero $e |- ( ( NX1 g39t7 g39t8 g39a1 ) mod 8 ) = 0 $.
  a9-g39i5-nonzero $e |- ( g39t7 ` ( NShift ( NA9 g39t8 g39a1 ) g39i5 ) ) =/= 0 $.
  a9-g39i6-nonzero $e |- ( g39t7 ` ( NShift ( NA9 g39t8 g39a1 ) g39i6 ) ) =/= 0 $.
  x3-nonzero $e |- ( NX3 g39t7 g39t8 g39a1 ) =/= 0 $.
  a14-g39i5-nonzero $e |- (
    g39t7 ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) g39i5 )
  ) =/= 0 $.
  a14-g39i6-nonzero $e |- (
    g39t7 ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) g39i6 )
  ) =/= 0 $.

  g39i-nonnegative $e |- 0 <_ g39i $.
  g39i-lt-g39size $e |- g39i < g39size $.
  g39i5-nonnegative $e |- 0 <_ g39i5 $.
  g39i5-lt-g39size $e |- g39i5 < g39size $.
  g39i6-nonnegative $e |- 0 <_ g39i6 $.
  g39i6-lt-g39size $e |- g39i6 < g39size $.
  g39i9-nonnegative $e |- 0 <_ g39i9 $.
  g39i9-le-g39size $e |- g39i9 <_ g39size $.
  x2-nonnegative $e |- 0 <_ ( NX2 g39t7 g39a1 ) $.
  x2-lt-g39size $e |- ( NX2 g39t7 g39a1 ) < g39size $.
  g39region-g39a $e |- ( g39region ` ( NBase g39a ) ) <_ 0 $.
  g39region-g39a1 $e |- ( g39region ` ( NBase g39a1 ) ) <_ 0 $.
  framed-g39t8 $e |- ( NFramed g39region g39t8 ) $.
  g39linked-t $e |- g39tm e. g39linked $.

  g39i-uint32 $e |- ( NUint32 g39i ) $.
  g39i1-uint32 $e |- ( NUint32 g39i1 ) $.
  g39i2-sint32 $e |- ( NSint32 g39i2 ) $.
  g39i3-sint32 $e |- ( NSint32 g39i3 ) $.
  g39i4-sint32 $e |- ( NSint32 g39i4 ) $.
  g39i7-sint32 $e |- ( NSint32 g39i7 ) $.
  g39i8-sint32 $e |- ( NSint32 g39i8 ) $.
  g39i9-sint32 $e |- ( NSint32 g39i9 ) $.
  g39i10-sint32 $e |- ( NSint32 g39i10 ) $.

  g39a1-valid $e |- ( NValidRD g39tm g39a1 5 ) $.
  x-uint32 $e |- ( NUint32 ( NX g39t7 g39a1 ) ) $.
  x2-sint32 $e |- ( NSint32 ( NX2 g39t7 g39a1 ) ) $.
  a6-valid $e |- ( NValidRD g39tm ( NA6 g39a1 ) 1 ) $.
  a10-valid $e |- ( NValidRD g39tm ( NA10 g39a1 ) 1 ) $.
  a2-valid $e |- ( NValidRD g39tm ( NA2 g39a1 ) 1 ) $.
  a3-valid $e |- ( NValidRD g39tm ( NA3 g39a1 ) 1 ) $.
  a15-valid $e |- ( NValidRD g39tm ( NA15 g39a g39i ) 1 ) $.
  a7-valid $e |- ( NValidRD g39tm ( NA7 g39t8 g39a1 ) 1 ) $.
  field2-valid $e |- ( NValidRD g39tm ( g39t8 ` ( NShift g39a1 2 ) ) 2 ) $.
  a4-valid $e |- ( NValidRD g39tm ( NA4 g39t8 g39a1 ) 2 ) $.
  x1-sint32 $e |- ( NSint32 ( NX1 g39t7 g39t8 g39a1 ) ) $.
  a16-valid $e |- ( NValidRD g39tm ( NA16 g39a g39i ) 1 ) $.
  a8-valid $e |- ( NValidRD g39tm ( NA8 g39t8 g39a1 ) 1 ) $.
  a11-valid $e |- ( NValidRD g39tm ( NA11 g39t8 g39a1 ) 1 ) $.
  a12-valid $e |- ( NValidRD g39tm ( NA12 g39t8 g39a1 ) 1 ) $.
  a13-valid $e |- ( NValidRD g39tm ( NA13 g39gbmask g39t8 g39a1 ) 1 ) $.
  x3-uint8 $e |- ( NUint8 ( NX3 g39t7 g39t8 g39a1 ) ) $.
  a18-valid $e |- ( NValidRD g39tm ( NA18 g39t8 g39a g39i ) g39size ) $.
  a19-valid $e |- ( NValidRD g39tm ( NA19 g39t8 g39a1 ) g39size ) $.
  a18-writable $e |- ( NValidRW g39tm ( NA18 g39t8 g39a g39i ) g39size ) $.
  a21-uint8 $e |- (
    NUint8 ( NA21 g39t6 g39t7 g39t8 g39a g39i g39size g39i8 g39a1 )
  ) $.
  a22-uint8 $e |- (
    NUint8 ( NA22 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i8 )
  ) $.
  a23-uint8 $e |- (
    NUint8 ( NA23 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i8 )
  ) $.
  a24-uint8 $e |- (
    NUint8 ( NA24 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i3 g39gbmask )
  ) $.
  a25-sint32 $e |- (
    NSint32 ( NA25 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 )
  ) $.
  a26-valid $e |- (
    NValidRD g39tm ( NA26 g39t8 g39gbmask g39t8 g39a1 ) g39size
  ) $.
  a18-a26-separated $e |- (
    NSeparated
      ( NA18 g39t8 g39a g39i ) g39size ( NA26 g39t8 g39gbmask g39t8 g39a1 ) g39size
  ) $.

  source-branch $e |- (
    (
      ( g39to_uint32 ` g39i8 ) < g39size
      ->
      (
        g39i10 = g39i8
        /\
        (
          g39t4 = g39tm
          /\
          (
            ( g39idle ` g39i10 ) =/= 0
            /\
            (
              if
              (
                ( NA27 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 ) = g39i10 ,
                1 , 0
              ) = g39i2
              /\
              (
                0 <_ g39i10
                /\
                (
                  g39i10 < g39size
                  /\
                  (
                    ( NValidRD g39t4 ( NA10 g39a1 ) 1 )
                    /\
                    (
                      ( NValidRD g39t4 ( NA3 g39a1 ) 1 )
                      /\
                      (
                        ( NValidRD g39t4 ( NA5 g39t8 g39a1 ) 1 )
                        /\
                        (
                          ( NX4 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 ) =/= 0
                          \/
                          (
                            g39size = g39i1
                            /\
                            (
                              NIdleCore
                                g39t8
                                ( NHavoc g39t6 g39t7 ( NA18 g39t8 g39a g39i ) g39i1 )
                                g39i10 g39i1 g39smtmask g39idle
                              /\
                              (
                                NMaskContext
                                  g39t4 g39t8 g39a g39i1
                                  g39sgcpus g39sgmask g39gbmask g39smtmask g39idle
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
      )
    )
    /\
    (
      -. ( ( g39to_uint32 ` g39i8 ) < g39size )
      ->
      (
        g39i4 = g39i3
        /\
        (
          g39t1 = g39tm
          /\
          (
            (
              g39i4 = ( -u 1 )
              ->
              (
                g39t2 = g39t1
                /\
                (
                  ( g39gbcpu ` ( NA12 g39t8 g39a1 ) ) = g39i7
                  /\
                  (
                    if
                    (
                      ( NA27 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 ) = g39i7 ,
                      1 , 0
                    ) = g39i2
                    /\
                    ( NValidRD g39t2 ( NA10 g39a1 ) 1 )
                  )
                )
              )
            )
            /\
            (
              g39i4 =/= ( -u 1 )
              ->
              (
                g39t3 = g39t1
                /\
                (
                  if
                  (
                    ( NA27 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 ) = g39i4 ,
                    1 , 0
                  ) = g39i2
                  /\
                  ( NValidRD g39t3 ( NA10 g39a1 ) 1 )
                )
              )
            )
          )
        )
      )
    )
  ) $.

  land-branch $e |- (
    ( NX4 g39t6 g39t7 g39t8 g39a g39i g39size g39a1 ) =/= 0
    -> g39i3 = ( -u 1 )
  ) $.

  g39i3-found-properties $e |- (
    g39i3 =/= ( -u 1 )
    ->
    (
      ( g39idle ` g39i3 ) =/= 0
      /\
      (
        ( NA22 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i8 ) =/= 0
        /\
        (
          ( NA24 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i3 g39gbmask ) =/= 0
          /\ ( 0 <_ g39i3 /\ g39i3 < g39size )
        )
      )
    )
  ) $.

  no-g39i3-transfers-mask $e |- (
    g39i3 = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
          ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < g39size
            ->
            (
              ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
              ` ( NShift ( NA17 g39t8 g39a g39i ) x )
            ) =/= 0
          )
        )
      )
  ) $.

  witness-g39i8-lt-g39size $e |- (
    (
      NDualWitness
        ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
        ( NA17 g39t8 g39a g39i ) ( NA9 g39t8 g39a1 )
        g39size ( NX5 g39to_uint32 g39i9 )
    )
    -> g39i8 < g39size
  ) $.

  witness-g39i8-bounds $e |- (
    (
      NDualWitness
        ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
        ( NA17 g39t8 g39a g39i ) ( NA9 g39t8 g39a1 )
        g39size ( NX5 g39to_uint32 g39i9 )
    )
    -> ( g39i8 < g39size /\ ( NX5 g39to_uint32 g39i9 ) <_ g39i8 )
  ) $.

  witness-selected-nonzero $e |- (
    (
      NDualWitness
        ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
        ( NA17 g39t8 g39a g39i ) ( NA9 g39t8 g39a1 )
        g39size ( NX5 g39to_uint32 g39i9 )
    )
    ->
    (
      ( NA21 g39t6 g39t7 g39t8 g39a g39i g39size g39i8 g39a1 ) =/= 0
      /\
      ( NA23 g39t6 g39t7 g39t8 g39a g39i g39size g39i3 g39a1 g39i8 ) =/= 0
    )
  ) $.

  all-tail-zero $e |- (
    (
      A. x e. ZZ
        (
          x < g39size
          ->
          (
            ( NX5 g39to_uint32 g39i9 ) <_ x
            ->
            (
              (
                ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
                ` ( NShift ( NA17 g39t8 g39a g39i ) x )
              ) = 0
              \/
              (
                ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
                ` ( NShift ( NA9 g39t8 g39a1 ) x )
              ) = 0
            )
          )
        )
    )
    -> g39size = g39i8
  ) $.

  prefix-g39idle-before-g39i3 $e |- (
    g39i3 =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
          ` ( NShift ( NA9 g39t8 g39a1 ) x )
        ) =/= 0
        ->
        (
          (
            ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
          ) =/= 0
          ->
          ( 0 <_ x -> ( x < g39i3 -> ( x < g39size -> ( g39idle ` x ) = 0 ) ) )
        )
      )
  ) $.

  prefix-g39idle-before-g39i9 $e |- (
    g39i3 = ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
          ` ( NShift ( NA9 g39t8 g39a1 ) x )
        ) =/= 0
        ->
        (
          (
            ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
          ) =/= 0
          ->
          ( 0 <_ x -> ( x < g39i9 -> ( x < g39size -> ( g39idle ` x ) = 0 ) ) )
        )
      )
  ) $.

  witness-zero-before-g39i8 $e |- (
    (
      NDualWitness
        ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
        ( NA17 g39t8 g39a g39i ) ( NA9 g39t8 g39a1 )
        g39size ( NX5 g39to_uint32 g39i9 )
    )
    ->
    A. x e. ZZ
      (
        x < g39i8
        ->
        (
          ( NX5 g39to_uint32 g39i9 ) <_ x
          ->
          (
            (
              ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
              ` ( NShift ( NA17 g39t8 g39a g39i ) x )
            ) = 0
            \/
            (
              ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
              ` ( NShift ( NA9 g39t8 g39a1 ) x )
            ) = 0
          )
        )
      )
  ) $.

  g39i3-to-g39i9-not-g39idle-core $e |- (
    g39i3 =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
          ` ( NShift ( NA9 g39t8 g39a1 ) x )
        ) =/= 0
        ->
        (
          (
            ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
          ) =/= 0
          ->
          (
            0 <_ x
            ->
            (
              g39i3 <_ x
              ->
              (
                x < g39i9
                ->
                (
                  x < g39size
                  ->
                  -. (
                    NIdleCore
                      g39t8 ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
                      x g39size g39smtmask g39idle
                  )
                )
              )
            )
          )
        )
      )
  ) $.

  found-or-not-g39idle-core $e |- (
    g39i3 =/= ( -u 1 )
    ->
    A. x e. ZZ
      (
        (
          ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
          ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
        ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < g39size
            ->
            (
              (
                ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
                ` ( NShift ( NA17 g39t8 g39a g39i ) x )
              ) =/= 0
              \/
              -. (
                NIdleCore
                  g39t8 ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
                  x g39size g39smtmask g39idle
              )
            )
          )
        )
      )
  ) $.

  a19-separated-storage $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < g39size
        ->
        (
          NSeparated
            ( NA19 g39t8 g39a1 ) g39size
            ( NStorage g39t8 ( NShift g39a x ) ) g39size
        )
      )
    ) $.

  cpu-storage-validity $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < g39size
        ->
        (
          ( NValidRD g39tm ( NShift g39a x ) 1 )
          /\ ( NValidRW g39tm ( NStorage g39t8 ( NShift g39a x ) ) g39size )
        )
      )
    ) $.

  a28-mask-equivalence $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < g39size
        ->
        (
          (
            ( NA28 g39t5 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
          ) =/= 0
          <->
          (
            ( NA28 g39t5 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA17 g39t8 g39a g39i ) x )
          ) =/= 0
        )
      )
    ) $.

  a20-a17-to-a14 $e |- A. x e. ZZ
    (
      (
        ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
        ` ( NShift ( NA17 g39t8 g39a g39i ) x )
      ) =/= 0
      ->
      (
        0 <_ x
        ->
        (
          x < g39size
          ->
          (
            ( NA20 g39t6 g39t7 g39t8 g39a g39i g39size )
            ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x )
          ) =/= 0
        )
      )
    ) $.

  original-not-g39idle-core $e |- A. x e. ZZ
    (
      ( g39t7 ` ( NShift ( NA9 g39t8 g39a1 ) x ) ) =/= 0
      ->
      (
        ( g39t7 ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x ) ) =/= 0
        ->
        (
          0 <_ x
          ->
          (
            x < g39size
            ->
            -. ( NIdleCore g39t8 g39t7 x g39size g39smtmask g39idle )
          )
        )
      )
    ) $.

  original-prefix-g39idle $e |- A. x e. ZZ
    (
      ( g39t7 ` ( NShift ( NA9 g39t8 g39a1 ) x ) ) =/= 0
      ->
      (
        ( g39t7 ` ( NShift ( NA14 g39t8 g39gbmask g39t8 g39a1 ) x ) ) =/= 0
        ->
        (
          0 <_ x
          ->
          ( x < g39i6 -> ( x < g39size -> ( g39idle ` x ) = 0 ) )
        )
      )
    ) $.

  final-mask-context $e |- (
    NMaskContext
      g39tm g39t8 g39a g39size g39sgcpus g39sgmask g39gbmask g39smtmask g39idle
  ) $.

  goal39 $a |- (
    ( ( NX2 g39t7 g39a1 ) = g39i6 ) <-> ( g39i2 =/= 0 )
  ) $.
$}
