$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_subqtvc: the verification condition
  for unequal-length multiprecision subtraction into a separate destination,
  including exact 32- and 64-bit word semantics, pointer validity and
  metadata, borrow propagation, copying of remaining limbs, one-limb
  functional updates, loop invariants, memory framing, and the final
  arithmetic relation. This file contains no proof.

  Pointer values retain an array with a total ZZ-indexed limb map and
  independent nonnegative-integer length metadata, together with integer
  offset and bounds, a writability bit, and an arbitrary nonempty zone.
  Functional updates and frame conditions are extensional over all integer
  addresses. The predicates below are definitional abbreviations for the
  source validity, value, metadata, update, frame, invariant, branch, and
  complete verification-condition formulas. Proposition-valued
  conditionals are rendered as equivalent exhaustive guarded disjunctions.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSameMeta
  NTP4VCUpdateLaw NTP4VCBounds NTP4VCOutsideFrame
  NTP4VCBorrowRange NTP4VCZeroFlag NTP4VCValueEq
  NTP4VCInitial NTP4VCFinal NTP4VCBorrowInvariant
  NTP4VCCopyInvariant NTP4VCCopyAfterUpdate NTP4VCCopyStep
  NTP4VCCopyLoop NTP4VCCopyPhase NTP4VCBorrowAfterIncrement
  NTP4VCBorrowAfterUpdate NTP4VCBorrowStep NTP4VCBorrowLoop
  NTP4VCBorrowPhase NTP4VCAfterInitialFlag NTP4VCAfterInitial
  NTP4VCVC
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
ntp4vc-same-meta-syn $a wff ( NTP4VCSameMeta A B ) $.
ntp4vc-update-law-syn
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-bounds-syn $a wff ( NTP4VCBounds A B ) $.
ntp4vc-outside-frame-syn
  $a wff ( NTP4VCOutsideFrame A B C ) $.
ntp4vc-borrow-range-syn $a wff ( NTP4VCBorrowRange A ) $.
ntp4vc-zero-flag-syn $a wff ( NTP4VCZeroFlag A B ) $.
ntp4vc-value-eq-syn
  $a wff ( NTP4VCValueEq A B C D E F ) $.
ntp4vc-initial-syn
  $a wff ( NTP4VCInitial A B C D E F ) $.
ntp4vc-final-syn
  $a wff ( NTP4VCFinal A B C D E F G ) $.
ntp4vc-borrow-invariant-syn
  $a wff ( NTP4VCBorrowInvariant A B C D E F G H ) $.
ntp4vc-copy-invariant-syn
  $a wff ( NTP4VCCopyInvariant A B C D E F G H ) $.
ntp4vc-copy-after-update-syn
  $a wff ( NTP4VCCopyAfterUpdate A B C D E F G H ) $.
ntp4vc-copy-step-syn
  $a wff ( NTP4VCCopyStep A B C D E F G H I ) $.
ntp4vc-copy-loop-syn
  $a wff ( NTP4VCCopyLoop A B C D E F G H ) $.
ntp4vc-copy-phase-syn
  $a wff ( NTP4VCCopyPhase A B C D E F G H I ) $.
ntp4vc-borrow-after-increment-syn
  $a wff ( NTP4VCBorrowAfterIncrement A B C D E F G H I J K ) $.
ntp4vc-borrow-after-update-syn
  $a wff ( NTP4VCBorrowAfterUpdate A B C D E F G H I J ) $.
ntp4vc-borrow-step-syn
  $a wff ( NTP4VCBorrowStep A B C D E F G H I ) $.
ntp4vc-borrow-loop-syn
  $a wff ( NTP4VCBorrowLoop A B C D E F G ) $.
ntp4vc-borrow-phase-syn
  $a wff ( NTP4VCBorrowPhase A B C D E F G H ) $.
ntp4vc-after-initial-flag-syn
  $a wff ( NTP4VCAfterInitialFlag A B C D E F G H I ) $.
ntp4vc-after-initial-syn
  $a wff ( NTP4VCAfterInitial A B C D E F G H ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C D E F ) $.

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
  ( ( NTP4VCWord64 ^m ZZ ) X. NN0 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) )
) $.

ntp4vc-data-def $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-length-def $a |- (
  NTP4VCLength A
) = ( 2nd ` ( NTP4VCData A ) ) $.

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
) = (
  ( 1st ` ( NTP4VCData A ) ) ` B
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

ntp4vc-same-meta-def $a |- (
  NTP4VCSameMeta A B
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

ntp4vc-borrow-range-def $a |- (
  NTP4VCBorrowRange A
) <-> (
  0 <_ A
  /\
  A <_ 1
) $.

ntp4vc-zero-flag-def $a |- (
  NTP4VCZeroFlag A B
) <-> (
  ( A = 0 -> B = 1 )
  /\
  ( B = 1 -> A = 0 )
) $.

ntp4vc-value-eq-def $a |- (
  NTP4VCValueEq A B C D E F
) <-> (
  (
    ( NTP4VCValue A D )
    -
    (
      ( NTP4VCRadix ^ ( NTP4VCToNat D ) )
      x.
      F
    )
  ) = (
    ( NTP4VCValue B D )
    -
    ( NTP4VCValue C E )
  )
) $.

ntp4vc-initial-def $a |- (
  NTP4VCInitial A B C D E F
) <-> (
  ( NTP4VCBorrowRange F )
  /\
  (
    (
      NTP4VCValueEq
        A C D
        ( NTP4VCSigned32 E )
        ( NTP4VCSigned32 E )
        F
    )
    /\
    (
      NTP4VCOutsideFrame
        A B ( NTP4VCSigned32 E )
    )
  )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D E F G
) <-> (
  (
    NTP4VCValueEq
      A C D
      ( NTP4VCSigned32 F )
      ( NTP4VCSigned32 E )
      G
  )
  /\
  (
    (
      NTP4VCOutsideFrame
        A B ( NTP4VCSigned32 F )
    )
    /\
    ( NTP4VCBorrowRange G )
  )
) $.

ntp4vc-borrow-invariant-def $a |- (
  NTP4VCBorrowInvariant A B C D E F G H
) <-> (
  (
    ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 G )
    /\
    ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 F )
  )
  /\
  (
    (
      NTP4VCValueEq
        A C D
        ( NTP4VCSigned32 G )
        ( NTP4VCSigned32 E )
        H
    )
    /\
    (
      (
        NTP4VCOutsideFrame
          A B ( NTP4VCSigned32 F )
      )
      /\
      (
        ( NTP4VCBorrowRange H )
        /\
        ( G = F \/ H = 1 )
      )
    )
  )
) $.

ntp4vc-copy-invariant-def $a |- (
  NTP4VCCopyInvariant A B C D E F G H
) <-> (
  (
    ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 G )
    /\
    ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 F )
  )
  /\
  (
    ( G = F \/ H = 0 )
    /\
    (
      (
        NTP4VCValueEq
          A C D
          ( NTP4VCSigned32 G )
          ( NTP4VCSigned32 E )
          H
      )
      /\
      (
        NTP4VCOutsideFrame
          A B ( NTP4VCSigned32 F )
      )
    )
  )
) $.

${
  $d o A B C D E F G H $.

  ntp4vc-copy-after-update-def $a |- (
    NTP4VCCopyAfterUpdate A B C D E F G H
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 G ) + 1 )
    )
    /\
    A. o e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 o
        ) = (
          ( NTP4VCSigned32 G ) + 1
        )
        ->
        (
          (
            0 <_ (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 G )
            )
            /\
            (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 o )
            ) < (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 G )
            )
          )
          /\
          (
            NTP4VCCopyInvariant
              A B C D E F o H
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H I $.

  ntp4vc-copy-step-def $a |- (
    NTP4VCCopyStep A B C D E F G H I
  ) <-> (
    (
      (
        ( NTP4VCSigned32 G )
        <
        ( NTP4VCSigned32 F )
      )
      /\
      (
        ( NTP4VCBounds C ( NTP4VCSigned32 G ) )
        /\
        (
          (
            ( NTP4VCBounds A ( NTP4VCSigned32 G ) )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          A. x e. ( NTP4VCPtr I )
            (
              ( NTP4VCSameMeta x A )
              ->
              (
                (
                  (
                    NTP4VCUpdateLaw
                      A x
                      (
                        ( NTP4VCOffset x )
                        +
                        ( NTP4VCSigned32 G )
                      )
                      (
                        NTP4VCPelts C
                          (
                            ( NTP4VCOffset C )
                            +
                            ( NTP4VCSigned32 G )
                          )
                      )
                  )
                  /\
                  (
                    NTP4VCPelts x
                      (
                        ( NTP4VCOffset x )
                        +
                        ( NTP4VCSigned32 G )
                      )
                  ) = (
                    NTP4VCPelts C
                      (
                        ( NTP4VCOffset C )
                        +
                        ( NTP4VCSigned32 G )
                      )
                  )
                )
                ->
                (
                  NTP4VCCopyAfterUpdate
                    x B C D E F G H
                )
              )
            )
        )
      )
    )
    \/
    (
      (
        ( NTP4VCSigned32 F )
        <_
        ( NTP4VCSigned32 G )
      )
      /\
      (
        NTP4VCFinal A B C D E F H
      )
    )
  ) $.
$}

${
  $d i x A B C D E F G H $.

  ntp4vc-copy-loop-def $a |- (
    NTP4VCCopyLoop A B C D E F G H
  ) <-> (
    A. i e. NTP4VCWord32
      A. x e. ( NTP4VCPtr H )
        (
          ( NTP4VCSameMeta x A )
          ->
          (
            (
              NTP4VCCopyInvariant
                x B C D E F i G
            )
            ->
            (
              NTP4VCCopyStep
                x B C D E F i G H
            )
          )
        )
  ) $.
$}

ntp4vc-copy-phase-def $a |- (
  NTP4VCCopyPhase A B C D E F G H I
) <-> (
  (
    NTP4VCCopyInvariant A B C D E F G H
  )
  /\
  (
    NTP4VCCopyLoop A B C D E F H I
  )
) $.

${
  $d b A B C D E F G H I J K $.

  ntp4vc-borrow-after-increment-def $a |- (
    NTP4VCBorrowAfterIncrement A B C D E F G H I J K
  ) <-> (
    A. b e. 2
      (
        ( NTP4VCZeroFlag J b )
        ->
        (
          (
            b =/= 1
            /\
            (
              NTP4VCCopyPhase
                A B C D E F I 0 K
            )
          )
          \/
          (
            b = 1
            /\
            (
              (
                0 <_ (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 G )
                )
                /\
                (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 I )
                ) < (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 G )
                )
              )
              /\
              (
                NTP4VCBorrowInvariant
                  A B C D E F I H
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d o A B C D E F G H I J $.

  ntp4vc-borrow-after-update-def $a |- (
    NTP4VCBorrowAfterUpdate A B C D E F G H I J
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 G ) + 1 )
    )
    /\
    A. o e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 o
        ) = (
          ( NTP4VCSigned32 G ) + 1
        )
        ->
        (
          NTP4VCBorrowAfterIncrement
            A B C D E F G H o I J
        )
      )
  ) $.
$}

${
  $d q x A B C D E F G H I $.

  ntp4vc-borrow-step-def $a |- (
    NTP4VCBorrowStep A B C D E F G H I
  ) <-> (
    (
      (
        ( NTP4VCSigned32 G )
        <
        ( NTP4VCSigned32 F )
      )
      /\
      (
        ( NTP4VCBounds C ( NTP4VCSigned32 G ) )
        /\
        A. q e. NTP4VCWord64
          (
            q = (
              (
                (
                  NTP4VCPelts C
                    (
                      ( NTP4VCOffset C )
                      +
                      ( NTP4VCSigned32 G )
                    )
                )
                -
                1
              )
              mod
              NTP4VCRadix
            )
            ->
            (
              (
                ( NTP4VCBounds A ( NTP4VCSigned32 G ) )
                /\
                ( NTP4VCWritable A ) = 1
              )
              /\
              A. x e. ( NTP4VCPtr I )
                (
                  ( NTP4VCSameMeta x A )
                  ->
                  (
                    (
                      (
                        NTP4VCUpdateLaw
                          A x
                          (
                            ( NTP4VCOffset x )
                            +
                            ( NTP4VCSigned32 G )
                          )
                          q
                      )
                      /\
                      (
                        NTP4VCPelts x
                          (
                            ( NTP4VCOffset x )
                            +
                            ( NTP4VCSigned32 G )
                          )
                      ) = q
                    )
                    ->
                    (
                      NTP4VCBorrowAfterUpdate
                        x B C D E F G H
                        (
                          NTP4VCPelts C
                            (
                              ( NTP4VCOffset C )
                              +
                              ( NTP4VCSigned32 G )
                            )
                        )
                        I
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
        ( NTP4VCSigned32 F )
        <_
        ( NTP4VCSigned32 G )
      )
      /\
      (
        NTP4VCCopyPhase A B C D E F G H I
      )
    )
  ) $.
$}

${
  $d i b x A B C D E F G $.

  ntp4vc-borrow-loop-def $a |- (
    NTP4VCBorrowLoop A B C D E F G
  ) <-> (
    A. i e. NTP4VCWord32
      A. b e. NTP4VCWord64
        A. x e. ( NTP4VCPtr G )
          (
            ( NTP4VCSameMeta x A )
            ->
            (
              (
                NTP4VCBorrowInvariant
                  x B C D E F i b
              )
              ->
              (
                NTP4VCBorrowStep
                  x B C D E F i b G
              )
            )
          )
  ) $.
$}

ntp4vc-borrow-phase-def $a |- (
  NTP4VCBorrowPhase A B C D E F G H
) <-> (
  (
    NTP4VCBorrowInvariant A B C D E F E G
  )
  /\
  (
    NTP4VCBorrowLoop A B C D E F H
  )
) $.

ntp4vc-after-initial-flag-def $a |- (
  NTP4VCAfterInitialFlag A B C D E F G H I
) <-> (
  (
    H =/= 1
    /\
    (
      NTP4VCBorrowPhase
        A B C D E F G I
    )
  )
  \/
  (
    H = 1
    /\
    (
      NTP4VCCopyPhase
        A B C D E F E G I
    )
  )
) $.

${
  $d b A B C D E F G H $.

  ntp4vc-after-initial-def $a |- (
    NTP4VCAfterInitial A B C D E F G H
  ) <-> (
    A. b e. 2
      (
        ( NTP4VCZeroFlag G b )
        ->
        (
          NTP4VCAfterInitialFlag
            A B C D E F G b H
        )
      )
  ) $.
$}

${
  $d x o A B C D E F $.

  ntp4vc-vc-def $a |- (
    NTP4VCVC A B C D E F
  ) <-> (
    (
      NTP4VCValid B ( NTP4VCSigned32 D )
    )
    /\
    (
      (
        NTP4VCValid C ( NTP4VCSigned32 D )
      )
      /\
      (
        (
          NTP4VCValid A ( NTP4VCSigned32 D )
        )
        /\
        (
          ( NTP4VCWritable A ) = 1
          /\
          A. x e. ( NTP4VCPtr F )
            (
              ( NTP4VCSameMeta x A )
              ->
              A. o e. NTP4VCWord64
                (
                  (
                    NTP4VCInitial
                      x A B C D o
                  )
                  ->
                  (
                    NTP4VCAfterInitial
                      x A B C D E o F
                  )
                )
            )
        )
      )
    )
  ) $.
$}

${
  $( Source theorem parameters:
     A=sy, B=sx, C=x, D=y, E=r, with zone Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sy-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-x-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-r-type $e |- E e. ( NTP4VCPtr Z ) $.
  ntp4vc-sy-nonnegative $e
    |- 0 <_ ( NTP4VCSigned32 A )
  $.
  ntp4vc-length-order $e
    |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B )
  $.
  ntp4vc-x-valid $e
    |- ( NTP4VCValid C ( NTP4VCSigned32 B ) )
  $.
  ntp4vc-y-valid $e
    |- ( NTP4VCValid D ( NTP4VCSigned32 A ) )
  $.
  ntp4vc-r-valid $e
    |- ( NTP4VCValid E ( NTP4VCSigned32 B ) )
  $.
  ntp4vc-r-writable $e |- ( NTP4VCWritable E ) = 1 $.

  ntp4vc-wmpn-sub-statement $a
    |- ( NTP4VCVC E C D A B Z )
  $.
$}
