$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decrqtvc: the verification
  condition for subtracting a 64-bit limb from a nonempty writable
  multiprecision unsigned integer in place, including modular limb updates,
  borrow propagation, loop invariants, pointer metadata, and memory framing.
  This file contains no proof.

  The 32- and 64-bit words use their complete canonical integer carriers,
  with exact two's-complement signed interpretation for 32-bit indices.
  Pointer data are finite 64-bit limb sequences; integer indexing uses the
  source Int.toNat behavior and a zero default outside the sequence. The
  predicates below are definitional factorizations of the source validity,
  value, pointer-shift, functional-update, frame, invariant, branch, and
  continuation formulas. Expanding them yields the original nested
  verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSamePelts
  NTP4VCFullShift NTP4VCStoreShape NTP4VCSnapshotMeta
  NTP4VCLoopPointer NTP4VCUpdateLaw NTP4VCBounds
  NTP4VCClosedBounds NTP4VCTailFrame NTP4VCOutsideFrame
  NTP4VCBoolResult NTP4VCFinal NTP4VCInitialInvariant
  NTP4VCLoopInvariant NTP4VCNextInvariant
  NTP4VCAfterIndexIncrement NTP4VCSecondWrite
  NTP4VCSecondResult NTP4VCLoopContinuation NTP4VCLoopStates
  NTP4VCBorrowBranch NTP4VCFirstWrite NTP4VCFirstResult
  NTP4VCShiftContinuation NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-radix-syn $a class NTP4VCRadix $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syn $a wff ( NTP4VCValid A B ) $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-same-pelts-syn $a wff ( NTP4VCSamePelts A B ) $.
ntp4vc-full-shift-syn $a wff ( NTP4VCFullShift A B C ) $.
ntp4vc-store-shape-syn $a wff ( NTP4VCStoreShape A B C ) $.
ntp4vc-snapshot-meta-syn $a wff ( NTP4VCSnapshotMeta A B ) $.
ntp4vc-loop-pointer-syn $a wff ( NTP4VCLoopPointer A B C ) $.
ntp4vc-update-law-syn $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-bounds-syn $a wff ( NTP4VCBounds A B ) $.
ntp4vc-closed-bounds-syn $a wff ( NTP4VCClosedBounds A B ) $.
ntp4vc-tail-frame-syn $a wff ( NTP4VCTailFrame A B C D ) $.
ntp4vc-outside-frame-syn $a wff ( NTP4VCOutsideFrame A B C ) $.
ntp4vc-bool-result-syn $a wff ( NTP4VCBoolResult A B ) $.
ntp4vc-final-syn $a wff ( NTP4VCFinal A B C D ) $.
ntp4vc-initial-invariant-syn
  $a wff ( NTP4VCInitialInvariant A B C D E ) $.
ntp4vc-loop-invariant-syn
  $a wff ( NTP4VCLoopInvariant A B C D E F G ) $.
ntp4vc-next-invariant-syn
  $a wff ( NTP4VCNextInvariant A B C D E F G H ) $.
ntp4vc-after-index-increment-syn
  $a wff ( NTP4VCAfterIndexIncrement A B C D E F G H I ) $.
ntp4vc-second-write-syn
  $a wff ( NTP4VCSecondWrite A B C D E F G H I ) $.
ntp4vc-second-result-syn
  $a wff ( NTP4VCSecondResult A B C D E F G H ) $.
ntp4vc-loop-continuation-syn
  $a wff ( NTP4VCLoopContinuation A B C D E F G H ) $.
ntp4vc-loop-states-syn
  $a wff ( NTP4VCLoopStates A B C D E ) $.
ntp4vc-borrow-branch-syn
  $a wff ( NTP4VCBorrowBranch A B C D E F ) $.
ntp4vc-first-write-syn
  $a wff ( NTP4VCFirstWrite A B C D E F G ) $.
ntp4vc-first-result-syn
  $a wff ( NTP4VCFirstResult A B C D E F ) $.
ntp4vc-shift-continuation-syn
  $a wff ( NTP4VCShiftContinuation A B C D E ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C D ) $.

ntp4vc-word32-def $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-def $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-def $a |- (
  NTP4VCSigned32 A
) = if (
  A < ( 2 ^ ; 3 1 ) ,
  A ,
  ( A - ( 2 ^ ; 3 2 ) )
) $.

ntp4vc-int32-in-bounds-def $a |- (
  NTP4VCInt32InBounds A
) <-> (
  A e. ZZ
  /\
  (
    ( -u ( 2 ^ ; 3 1 ) ) <_ A
    /\
    A < ( 2 ^ ; 3 1 )
  )
) $.

ntp4vc-radix-def $a |- NTP4VCRadix = ( 2 ^ ; 6 4 ) $.

ntp4vc-ptr-def $a |- (
  NTP4VCPtr A
) = (
  ( Word NTP4VCWord64 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) )
) $.

ntp4vc-data-def $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-length-def $a |- (
  NTP4VCLength A
) = ( # ` ( NTP4VCData A ) ) $.

ntp4vc-offset-def $a |- (
  NTP4VCOffset A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-def $a |- (
  NTP4VCMin A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-def $a |- (
  NTP4VCMax A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-writable-def $a |- (
  NTP4VCWritable A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-zone-def $a |- (
  NTP4VCZone A
) = ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-to-nat-def $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-pelts-def $a |- (
  NTP4VCPelts A B
) = if (
  ( NTP4VCToNat B ) < ( NTP4VCLength A ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-valid-def $a |- (
  NTP4VCValid A B
) <-> (
  ( NTP4VCInt32InBounds B )
  /\
  (
    0 <_ B
    /\
    (
      (
        0 <_ ( NTP4VCMin A )
        /\
        ( NTP4VCMin A ) <_ ( NTP4VCOffset A )
      )
      /\
      (
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A )
        /\
        ( NTP4VCMax A ) <_ ( NTP4VCLength A )
      )
    )
  )
) $.

${
  $d k A B $.

  ntp4vc-value-def $a |- (
    NTP4VCValue A B
  ) = (
    sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
      (
        ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) )
        x.
        ( NTP4VCRadix ^ k )
      )
  ) $.
$}

${
  $d j A B $.

  ntp4vc-same-pelts-def $a |- (
    NTP4VCSamePelts A B
  ) <-> (
    A. j e. ZZ
      ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
  ) $.
$}

ntp4vc-full-shift-def $a |- (
  NTP4VCFullShift A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( NTP4VCLength A ) = ( NTP4VCLength B )
    /\
    (
      ( NTP4VCSamePelts A B )
      /\
      (
        ( NTP4VCData A ) = ( NTP4VCData B )
        /\
        (
          ( NTP4VCMin A ) = ( NTP4VCMin B )
          /\
          (
            ( NTP4VCMax A ) = ( NTP4VCMax B )
            /\
            (
              ( NTP4VCZone A ) = ( NTP4VCZone B )
              /\
              ( NTP4VCWritable A ) = ( NTP4VCWritable B )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-store-shape-def $a |- (
  NTP4VCStoreShape A B C
) <-> (
  ( NTP4VCData A ) = ( NTP4VCData B )
  /\
  (
    ( NTP4VCLength B ) = ( NTP4VCLength C )
    /\
    (
      ( NTP4VCOffset A ) = ( NTP4VCOffset C )
      /\
      (
        ( NTP4VCMin A ) = ( NTP4VCMin C )
        /\
        (
          ( NTP4VCMax A ) = ( NTP4VCMax C )
          /\
          (
            ( NTP4VCWritable A ) = ( NTP4VCWritable C )
            /\
            ( NTP4VCZone A ) = ( NTP4VCZone C )
          )
        )
      )
    )
  )
) $.

ntp4vc-snapshot-meta-def $a |- (
  NTP4VCSnapshotMeta A B
) <-> (
  ( NTP4VCLength A ) = ( NTP4VCLength B )
  /\
  (
    ( NTP4VCOffset A ) = ( NTP4VCOffset B )
    /\
    (
      ( NTP4VCMin A ) = ( NTP4VCMin B )
      /\
      (
        ( NTP4VCMax A ) = ( NTP4VCMax B )
        /\
        (
          ( NTP4VCWritable A ) = ( NTP4VCWritable B )
          /\
          ( NTP4VCZone A ) = ( NTP4VCZone B )
        )
      )
    )
  )
) $.

ntp4vc-loop-pointer-def $a |- (
  NTP4VCLoopPointer A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( NTP4VCSamePelts A B )
    /\
    (
      ( NTP4VCLength A ) = ( NTP4VCLength B )
      /\
      (
        ( NTP4VCMin A ) = ( NTP4VCMin B )
        /\
        ( NTP4VCMax A ) = ( NTP4VCMax B )
      )
    )
  )
) $.

${
  $d j A B C D $.

  ntp4vc-update-law-def $a |- (
    NTP4VCUpdateLaw A B C D
  ) <-> (
    A. j e. ZZ
      (
        ( NTP4VCPelts B j )
        =
        if (
          j = C ,
          D ,
          ( NTP4VCPelts A j )
        )
      )
  ) $.
$}

ntp4vc-bounds-def $a |- (
  NTP4VCBounds A B
) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A )
) $.

ntp4vc-closed-bounds-def $a |- (
  NTP4VCClosedBounds A B
) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A )
) $.

${
  $d j A B C D $.

  ntp4vc-tail-frame-def $a |- (
    NTP4VCTailFrame A B C D
  ) <-> (
    A. j e. ZZ
      (
        (
          C <_ j
          /\
          j < D
        )
        ->
        (
          NTP4VCPelts A ( ( NTP4VCOffset A ) + j )
        ) = (
          NTP4VCPelts B ( ( NTP4VCOffset A ) + j )
        )
      )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-outside-frame-def $a |- (
    NTP4VCOutsideFrame A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          j < ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + C ) <_ j
        )
        ->
        ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
      )
  ) $.
$}

ntp4vc-bool-result-def $a |- (
  NTP4VCBoolResult A B
) <-> (
  ( A = 0 -> B = 1 )
  /\
  ( B = 1 -> A = 0 )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D
) <-> (
  (
    NTP4VCValue A ( NTP4VCSigned32 C )
  ) = (
    ( NTP4VCValue B ( NTP4VCSigned32 C ) )
    -
    D
  )
  /\
  ( NTP4VCOutsideFrame A B ( NTP4VCSigned32 C ) )
) $.

ntp4vc-initial-invariant-def $a |- (
  NTP4VCInitialInvariant A B C D E
) <-> (
  (
    1 <_ 1
    /\
    1 <_ ( NTP4VCSigned32 D )
  )
  /\
  (
    ( NTP4VCLoopPointer A B 1 )
    /\
    (
      ( 1 = D -> 1 = 0 )
      /\
      (
        (
          0 <_ 1
          /\
          1 <_ 1
        )
        /\
        (
          ( NTP4VCWritable A ) = 1
          /\
          (
            (
              ( NTP4VCValue B 1 )
              -
              ( ( NTP4VCRadix ^ 1 ) x. 1 )
            ) = (
              ( NTP4VCValue C 1 ) - E
            )
            /\
            (
              ( NTP4VCTailFrame B C 1 ( NTP4VCSigned32 D ) )
              /\
              ( NTP4VCOutsideFrame B C ( NTP4VCSigned32 D ) )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-loop-invariant-def $a |- (
  NTP4VCLoopInvariant A B C D E F G
) <-> (
  (
    1 <_ ( NTP4VCSigned32 B )
    /\
    ( NTP4VCSigned32 B ) <_ ( NTP4VCSigned32 F )
  )
  /\
  (
    ( NTP4VCLoopPointer A D ( NTP4VCSigned32 B ) )
    /\
    (
      ( B = F -> C = 0 )
      /\
      (
        (
          0 <_ C
          /\
          C <_ 1
        )
        /\
        (
          ( NTP4VCWritable A ) = 1
          /\
          (
            (
              ( NTP4VCValue D ( NTP4VCSigned32 B ) )
              -
              (
                (
                  NTP4VCRadix
                  ^
                  ( NTP4VCToNat ( NTP4VCSigned32 B ) )
                )
                x.
                C
              )
            ) = (
              ( NTP4VCValue E ( NTP4VCSigned32 B ) )
              -
              G
            )
            /\
            (
              (
                NTP4VCTailFrame
                  D E
                  ( NTP4VCSigned32 B )
                  ( NTP4VCSigned32 F )
              )
              /\
              (
                NTP4VCOutsideFrame
                  D E ( NTP4VCSigned32 F )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-next-invariant-def $a |- (
  NTP4VCNextInvariant A B C D E F G H
) <-> (
  (
    0 <_ (
      ( NTP4VCSigned32 G )
      -
      ( NTP4VCSigned32 B )
    )
    /\
    (
      ( NTP4VCSigned32 G )
      -
      ( NTP4VCSigned32 C )
    ) < (
      ( NTP4VCSigned32 G )
      -
      ( NTP4VCSigned32 B )
    )
  )
  /\
  ( NTP4VCLoopInvariant A C D E F G H )
) $.

${
  $d r p o A B C D E F G H I $.

  ntp4vc-after-index-increment-def $a |- (
    NTP4VCAfterIndexIncrement A B C D E F G H I
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) + 1 )
    )
    /\
    A. r e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 r
        ) = (
          ( NTP4VCSigned32 D ) + 1
        )
        ->
        (
          ( NTP4VCClosedBounds A 1 )
          /\
          A. p e. ( NTP4VCPtr I )
            (
              ( NTP4VCFullShift p A 1 )
              ->
              A. o e. 2
                (
                  ( NTP4VCBoolResult H o )
                  ->
                  (
                    (
                      o =/= 1
                      /\
                      ( NTP4VCFinal B C E G )
                    )
                    \/
                    (
                      o = 1
                      /\
                      (
                        NTP4VCNextInvariant
                          p D r F B C E G
                      )
                    )
                  )
                )
            )
        )
      )
  ) $.
$}

${
  $d p q A B C D E F G H I $.

  ntp4vc-second-write-def $a |- (
    NTP4VCSecondWrite A B C D E F G H I
  ) <-> (
    A. p e. ( NTP4VCPtr I )
      A. q e. ( NTP4VCPtr I )
        (
          ( NTP4VCStoreShape p q A )
          ->
          (
            ( NTP4VCStoreShape p q A )
            ->
            (
              ( NTP4VCSnapshotMeta q B )
              ->
              (
                ( NTP4VCUpdateLaw A p ( NTP4VCOffset p ) H )
                ->
                (
                  NTP4VCAfterIndexIncrement
                    p q C D E F G
                    ( NTP4VCPelts A ( NTP4VCOffset A ) )
                    I
                )
              )
            )
          )
        )
  ) $.
$}

${
  $d r A B C D E F G H $.

  ntp4vc-second-result-def $a |- (
    NTP4VCSecondResult A B C D E F G H
  ) <-> (
    ( NTP4VCBounds A 0 )
    /\
    A. r e. NTP4VCWord64
      (
        r = (
          (
            ( NTP4VCPelts A ( NTP4VCOffset A ) )
            -
            1
          )
          mod
          NTP4VCRadix
        )
        ->
        (
          (
            ( NTP4VCBounds A 0 )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          ( NTP4VCSecondWrite A B C D E F G r H )
        )
      )
  ) $.
$}

${
  $d o A B C D E F G H $.

  ntp4vc-loop-continuation-def $a |- (
    NTP4VCLoopContinuation A B C D E F G H
  ) <-> (
    A. o e. 2
      (
        ( NTP4VCBoolResult F o )
        ->
        (
          (
            o =/= 1
            /\
            ( NTP4VCSecondResult A B C D E F G H )
          )
          \/
          (
            o = 1
            /\
            ( NTP4VCFinal B C E G )
          )
        )
      )
  ) $.
$}

${
  $d i p b q A B C D E $.

  ntp4vc-loop-states-def $a |- (
    NTP4VCLoopStates A B C D E
  ) <-> (
    A. i e. NTP4VCWord32
      A. p e. ( NTP4VCPtr E )
        A. b e. NTP4VCWord64
          A. q e. ( NTP4VCPtr E )
            (
              ( NTP4VCSnapshotMeta q A )
              ->
              (
                ( NTP4VCLoopInvariant p i b q B C D )
                ->
                (
                  NTP4VCLoopContinuation
                    p q B i C b D E
                )
              )
            )
  ) $.
$}

ntp4vc-borrow-branch-def $a |- (
  NTP4VCBorrowBranch A B C D E F
) <-> (
  ( NTP4VCInitialInvariant A B C D E )
  /\
  ( NTP4VCLoopStates B C D E F )
) $.

${
  $d p q A B C D E F G $.

  ntp4vc-first-write-def $a |- (
    NTP4VCFirstWrite A B C D E F G
  ) <-> (
    A. p e. ( NTP4VCPtr G )
      A. q e. ( NTP4VCPtr G )
        (
          ( NTP4VCStoreShape p q A )
          ->
          (
            ( NTP4VCSnapshotMeta q B )
            ->
            (
              ( NTP4VCUpdateLaw B q ( NTP4VCOffset q ) F )
              ->
              (
                (
                  E < F
                  /\
                  ( NTP4VCBorrowBranch p q B C D G )
                )
                \/
                (
                  ( -. ( E < F ) )
                  /\
                  ( NTP4VCFinal q B C D )
                )
              )
            )
          )
        )
  ) $.
$}

${
  $d r A B C D E F $.

  ntp4vc-first-result-def $a |- (
    NTP4VCFirstResult A B C D E F
  ) <-> (
    A. r e. NTP4VCWord64
      (
        r = (
          ( E - D )
          mod
          NTP4VCRadix
        )
        ->
        (
          (
            ( NTP4VCBounds B 0 )
            /\
            ( NTP4VCWritable B ) = 1
          )
          /\
          ( NTP4VCFirstWrite A B C D E r F )
        )
      )
  ) $.
$}

${
  $d p A B C D E $.

  ntp4vc-shift-continuation-def $a |- (
    NTP4VCShiftContinuation A B C D E
  ) <-> (
    A. p e. ( NTP4VCPtr E )
      (
        ( NTP4VCFullShift p A 1 )
        ->
        ( NTP4VCFirstResult p A B C D E )
      )
  ) $.
$}

ntp4vc-vc-def $a |- (
  NTP4VCVC A B C D
) <-> (
  ( NTP4VCBounds A 0 )
  /\
  (
    ( NTP4VCClosedBounds A 1 )
    /\
    (
      NTP4VCShiftContinuation
        A B C
        ( NTP4VCPelts A ( NTP4VCOffset A ) )
        D
    )
  )
) $.

${
  $( Source parameters: A=x, B=sz, C=y, with common zone carrier Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-y-type $e |- C e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-fact2 $e |- 0 <_ (
    ( NTP4VCValue A ( NTP4VCSigned32 B ) )
    -
    C
  ) $.
  ntp4vc-fact3 $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-decr-statement $a |- (
    NTP4VCVC A B C Z
  ) $.
$}
