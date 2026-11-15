$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_nqtvc: the verification condition
  for equal-length multiprecision subtraction into a separate destination,
  including exact 32- and 64-bit word semantics, pointer validity and
  metadata, borrow propagation, one-limb functional update, loop invariants,
  memory framing, and the final arithmetic relation. This file contains no
  proof.

  Pointer values retain an array with a total ZZ-indexed limb map and
  independent nonnegative-integer length metadata, together with integer
  offset and bounds, a writability bit, and an arbitrary nonempty zone.
  Functional updates and frame conditions are extensional over all integer
  addresses. The predicates below are definitional abbreviations for the
  source validity, value, metadata, update, frame, invariant, branch, and
  complete verification-condition formulas. The proposition-valued
  conditional is rendered as an equivalent exhaustive guarded disjunction.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSameMeta
  NTP4VCUpdateLaw NTP4VCBounds NTP4VCOutsideFrame
  NTP4VCInvariant NTP4VCFinal NTP4VCNext NTP4VCAfterWrite
  NTP4VCThenBranch NTP4VCLoopBody NTP4VCVC
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
ntp4vc-invariant-syn
  $a wff ( NTP4VCInvariant A B C D E F G ) $.
ntp4vc-final-syn
  $a wff ( NTP4VCFinal A B C D E F ) $.
ntp4vc-next-syn
  $a wff ( NTP4VCNext A B C D E F G H ) $.
ntp4vc-after-write-syn
  $a wff ( NTP4VCAfterWrite A B C D E F G H I ) $.
ntp4vc-then-branch-syn
  $a wff ( NTP4VCThenBranch A B C D E F G H ) $.
ntp4vc-loop-body-syn
  $a wff ( NTP4VCLoopBody A B C D E F G H ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C D E ) $.

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

ntp4vc-invariant-def $a |- (
  NTP4VCInvariant A B C D E F G
) <-> (
  (
    0 <_ ( NTP4VCSigned32 E )
    /\
    ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 G )
  )
  /\
  (
    (
      (
        NTP4VCValue A ( NTP4VCSigned32 E )
      )
      -
      (
        (
          NTP4VCRadix
          ^
          ( NTP4VCToNat ( NTP4VCSigned32 E ) )
        )
        x.
        F
      )
    ) = (
      (
        NTP4VCValue C ( NTP4VCSigned32 E )
      )
      -
      (
        NTP4VCValue D ( NTP4VCSigned32 E )
      )
    )
    /\
    (
      (
        NTP4VCOutsideFrame
          A B ( NTP4VCSigned32 G )
      )
      /\
      (
        0 <_ F
        /\
        F <_ 1
      )
    )
  )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D E F
) <-> (
  (
    0 <_ E
    /\
    E <_ 1
  )
  /\
  (
    (
      (
        NTP4VCValue A ( NTP4VCSigned32 F )
      )
      -
      (
        (
          NTP4VCRadix
          ^
          ( NTP4VCToNat ( NTP4VCSigned32 F ) )
        )
        x.
        E
      )
    ) = (
      (
        NTP4VCValue C ( NTP4VCSigned32 F )
      )
      -
      (
        NTP4VCValue D ( NTP4VCSigned32 F )
      )
    )
    /\
    (
      NTP4VCOutsideFrame
        A B ( NTP4VCSigned32 F )
    )
  )
) $.

ntp4vc-next-def $a |- (
  NTP4VCNext A B C D E F G H
) <-> (
  (
    0 <_ (
      ( NTP4VCSigned32 H )
      -
      ( NTP4VCSigned32 G )
    )
    /\
    (
      ( NTP4VCSigned32 H )
      -
      ( NTP4VCSigned32 E )
    ) < (
      ( NTP4VCSigned32 H )
      -
      ( NTP4VCSigned32 G )
    )
  )
  /\
  (
    NTP4VCInvariant A B C D E F H
  )
) $.

${
  $d x o A B C D E F G H I $.

  ntp4vc-after-write-def $a |- (
    NTP4VCAfterWrite A B C D E F G H I
  ) <-> (
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
                  ( NTP4VCSigned32 E )
                )
                F
            )
            /\
            (
              NTP4VCPelts x
                (
                  ( NTP4VCOffset x )
                  +
                  ( NTP4VCSigned32 E )
                )
            ) = F
          )
          ->
          (
            (
              NTP4VCInt32InBounds
                ( ( NTP4VCSigned32 E ) + 1 )
            )
            /\
            A. o e. NTP4VCWord32
              (
                (
                  NTP4VCSigned32 o
                ) = (
                  ( NTP4VCSigned32 E ) + 1
                )
                ->
                (
                  NTP4VCNext x B C D o G E H
                )
              )
          )
        )
      )
  ) $.
$}

${
  $d q c A B C D E F G H $.

  ntp4vc-then-branch-def $a |- (
    NTP4VCThenBranch A B C D E F G H
  ) <-> (
    (
      NTP4VCBounds C ( NTP4VCSigned32 E )
    )
    /\
    (
      (
        NTP4VCBounds D ( NTP4VCSigned32 E )
      )
      /\
      (
        (
          0 <_ F
          /\
          F <_ 1
        )
        /\
        A. q e. NTP4VCWord64
          A. c e. NTP4VCWord64
            (
              (
                (
                  q
                  -
                  ( NTP4VCRadix x. c )
                ) = (
                  (
                    NTP4VCPelts C
                      (
                        ( NTP4VCOffset C )
                        +
                        ( NTP4VCSigned32 E )
                      )
                  )
                  -
                  (
                    NTP4VCPelts D
                      (
                        ( NTP4VCOffset D )
                        +
                        ( NTP4VCSigned32 E )
                      )
                  )
                  -
                  F
                )
                /\
                (
                  0 <_ c
                  /\
                  c <_ 1
                )
              )
              ->
              (
                (
                  (
                    NTP4VCBounds A ( NTP4VCSigned32 E )
                  )
                  /\
                  ( NTP4VCWritable A ) = 1
                )
                /\
                (
                  NTP4VCAfterWrite
                    A B C D E q c G H
                )
              )
            )
      )
    )
  ) $.
$}

ntp4vc-loop-body-def $a |- (
  NTP4VCLoopBody A B C D E F G H
) <-> (
  (
    (
      ( NTP4VCSigned32 E )
      <
      ( NTP4VCSigned32 G )
    )
    /\
    (
      NTP4VCThenBranch A B C D E F G H
    )
  )
  \/
  (
    (
      ( NTP4VCSigned32 G )
      <_
      ( NTP4VCSigned32 E )
    )
    /\
    (
      NTP4VCFinal A B C D F G
    )
  )
) $.

${
  $d i b x A B C D E $.

  ntp4vc-vc-def $a |- (
    NTP4VCVC A B C D E
  ) <-> (
    0 <_ 0
    /\
    (
      0 <_ ( NTP4VCSigned32 D )
      /\
      (
        (
          (
            NTP4VCValue A 0
          )
          -
          (
            ( NTP4VCRadix ^ 0 )
            x.
            0
          )
        ) = (
          ( NTP4VCValue B 0 )
          -
          ( NTP4VCValue C 0 )
        )
        /\
        (
          0 <_ 0
          /\
          (
            0 <_ 1
            /\
            A. i e. NTP4VCWord32
              A. b e. NTP4VCWord64
                A. x e. ( NTP4VCPtr E )
                  (
                    ( NTP4VCSameMeta x A )
                    ->
                    (
                      (
                        NTP4VCInvariant x A B C i b D
                      )
                      ->
                      (
                        NTP4VCLoopBody x A B C i b D E
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
  $( Source theorem parameters: A=x, B=y, C=r, D=sz, with zone Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-r-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- D e. NTP4VCWord32 $.
  ntp4vc-x-valid $e
    |- ( NTP4VCValid A ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-y-valid $e
    |- ( NTP4VCValid B ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-r-valid $e
    |- ( NTP4VCValid C ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-r-writable $e |- ( NTP4VCWritable C ) = 1 $.

  ntp4vc-wmpn-sub-n-statement $a
    |- ( NTP4VCVC C A B D Z )
  $.
$}
