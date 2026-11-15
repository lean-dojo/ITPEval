$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_decr_1qtvc: the verification
  condition for decrementing a valid writable multiprecision unsigned
  integer in place, including borrow propagation, one-limb modular updates,
  pointer metadata, loop invariants, and memory framing. This file contains
  no proof.

  Unsigned 32- and 64-bit words use their complete canonical integer
  carriers, and signed 32-bit interpretation is exact two's complement.
  A pointer contains a total ZZ-indexed 64-bit limb map with independent
  nonnegative length metadata, integer offset and bounds, a writability bit,
  and an arbitrary nonempty zone. The helper predicates below are
  definitional factorizations of the source validity, positional value,
  pointer-shift, functional-update, frame, invariant, and branch formulas.
  Expanding them yields the original nested universal verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCPeltsMap
  NTP4VCOffset NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone
  NTP4VCToNat NTP4VCPelts NTP4VCValid NTP4VCValue
  NTP4VCSameMeta NTP4VCFullShift NTP4VCViewShift NTP4VCAlias
  NTP4VCUpdateLaw NTP4VCBounds NTP4VCClosedBounds
  NTP4VCTailFrame NTP4VCOutsideFrame NTP4VCBoolResult
  NTP4VCBorrowLink NTP4VCInitialInvariant NTP4VCLoopInvariant
  NTP4VCNextInvariant NTP4VCFinal NTP4VCAfterWrite
  NTP4VCWriteCase NTP4VCO3Continuation NTP4VCO2True
  NTP4VCO2Continuation NTP4VCContinuation NTP4VCVC
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
ntp4vc-pelts-map-syn $a class ( NTP4VCPeltsMap A ) $.
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
ntp4vc-full-shift-syn $a wff ( NTP4VCFullShift A B C ) $.
ntp4vc-view-shift-syn $a wff ( NTP4VCViewShift A B C ) $.
ntp4vc-alias-syn $a wff ( NTP4VCAlias A B C ) $.
ntp4vc-update-law-syn $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-bounds-syn $a wff ( NTP4VCBounds A B ) $.
ntp4vc-closed-bounds-syn $a wff ( NTP4VCClosedBounds A B ) $.
ntp4vc-tail-frame-syn $a wff ( NTP4VCTailFrame A B C D ) $.
ntp4vc-outside-frame-syn $a wff ( NTP4VCOutsideFrame A B C ) $.
ntp4vc-bool-result-syn $a wff ( NTP4VCBoolResult A B ) $.
ntp4vc-borrow-link-syn $a wff ( NTP4VCBorrowLink A B ) $.
ntp4vc-initial-invariant-syn
  $a wff ( NTP4VCInitialInvariant A B C ) $.
ntp4vc-loop-invariant-syn
  $a wff ( NTP4VCLoopInvariant A B C D E F G ) $.
ntp4vc-next-invariant-syn
  $a wff ( NTP4VCNextInvariant A B C D E F G H ) $.
ntp4vc-final-syn $a wff ( NTP4VCFinal A B C ) $.
ntp4vc-after-write-syn
  $a wff ( NTP4VCAfterWrite A B C D E F G H I ) $.
ntp4vc-write-case-syn
  $a wff ( NTP4VCWriteCase A B C D E F G H I ) $.
ntp4vc-o3-continuation-syn
  $a wff ( NTP4VCO3Continuation A B C D E F G ) $.
ntp4vc-o2-true-syn
  $a wff ( NTP4VCO2True A B C D E F ) $.
ntp4vc-o2-continuation-syn
  $a wff ( NTP4VCO2Continuation A B C D E F G ) $.
ntp4vc-continuation-syn
  $a wff ( NTP4VCContinuation A B C D ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C ) $.

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
  ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) )
) $.

ntp4vc-data-def $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-length-def $a |- (
  NTP4VCLength A
) = ( 2nd ` ( NTP4VCData A ) ) $.

ntp4vc-pelts-map-def $a |- (
  NTP4VCPeltsMap A
) = ( 1st ` ( NTP4VCData A ) ) $.

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
) = ( ( NTP4VCPeltsMap A ) ` B ) $.

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

ntp4vc-full-shift-def $a |- (
  NTP4VCFullShift A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( NTP4VCLength A ) = ( NTP4VCLength B )
    /\
    (
      ( NTP4VCPeltsMap A ) = ( NTP4VCPeltsMap B )
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

ntp4vc-view-shift-def $a |- (
  NTP4VCViewShift A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( NTP4VCPeltsMap A ) = ( NTP4VCPeltsMap B )
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

ntp4vc-alias-def $a |- (
  NTP4VCAlias A B C
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

ntp4vc-borrow-link-def $a |- (
  NTP4VCBorrowLink A B
) <-> (
  A =/= 0
  <->
  B = 0
) $.

ntp4vc-initial-invariant-def $a |- (
  NTP4VCInitialInvariant A B C
) <-> (
  (
    0 <_ 0
    /\
    0 <_ ( NTP4VCSigned32 C )
  )
  /\
  (
    0 =/= C
    /\
    (
      ( NTP4VCViewShift A B 0 )
      /\
      (
        1 =/= 0
        /\
        (
          (
            0 <_ 1
            /\
            1 <_ 1
          )
          /\
          (
            (
              ( NTP4VCValue B 0 )
              -
              ( ( NTP4VCRadix ^ 0 ) x. 1 )
            )
            =
            ( ( NTP4VCValue B 0 ) - 1 )
            /\
            ( NTP4VCWritable A ) = 1
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
    0 <_ ( NTP4VCSigned32 B )
    /\
    ( NTP4VCSigned32 B ) <_ ( NTP4VCSigned32 G )
  )
  /\
  (
    (
      B = G
      ->
      C =/= 0
    )
    /\
    (
      ( NTP4VCViewShift A E ( NTP4VCSigned32 B ) )
      /\
      (
        ( NTP4VCBorrowLink C D )
        /\
        (
          (
            0 <_ D
            /\
            D <_ 1
          )
          /\
          (
            (
              ( NTP4VCValue E ( NTP4VCSigned32 B ) )
              -
              (
                ( NTP4VCRadix ^ ( NTP4VCSigned32 B ) )
                x.
                D
              )
            )
            =
            (
              ( NTP4VCValue F ( NTP4VCSigned32 B ) )
              -
              1
            )
            /\
            (
              ( NTP4VCWritable A ) = 1
              /\
              (
                (
                  NTP4VCTailFrame
                    E F
                    ( NTP4VCSigned32 B )
                    ( NTP4VCSigned32 G )
                )
                /\
                (
                  NTP4VCOutsideFrame
                    E F
                    ( NTP4VCSigned32 G )
                )
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
      ( NTP4VCSigned32 D )
      -
      ( NTP4VCSigned32 E )
    )
    /\
    (
      ( NTP4VCSigned32 D )
      -
      ( NTP4VCSigned32 F )
    ) < (
      ( NTP4VCSigned32 D )
      -
      ( NTP4VCSigned32 E )
    )
  )
  /\
  (
    NTP4VCLoopInvariant A F G H B C D
  )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C
) <-> (
  (
    NTP4VCValue A ( NTP4VCSigned32 C )
  ) = (
    ( NTP4VCValue B ( NTP4VCSigned32 C ) )
    -
    1
  )
  /\
  (
    NTP4VCOutsideFrame A B ( NTP4VCSigned32 C )
  )
) $.

${
  $d p q r s A B C D E F G H I $.

  ntp4vc-after-write-def $a |- (
    NTP4VCAfterWrite A B C D E F G H I
  ) <-> (
    A. p e. ( NTP4VCPtr I )
      A. q e. ( NTP4VCPtr I )
        (
          ( NTP4VCAlias p q A )
          ->
          (
            ( NTP4VCAlias p q A )
            ->
            (
              ( NTP4VCSameMeta q B )
              ->
              (
                (
                  NTP4VCUpdateLaw
                    A p ( NTP4VCOffset p ) F
                )
                ->
                (
                  (
                    NTP4VCInt32InBounds
                      ( ( NTP4VCSigned32 E ) + 1 )
                  )
                  /\
                  A. r e. NTP4VCWord32
                    (
                      (
                        NTP4VCSigned32 r
                      ) = (
                        ( NTP4VCSigned32 E ) + 1
                      )
                      ->
                      (
                        ( NTP4VCClosedBounds p 1 )
                        /\
                        A. s e. ( NTP4VCPtr I )
                          (
                            ( NTP4VCFullShift s p 1 )
                            ->
                            (
                              NTP4VCNextInvariant
                                s q C D E r G H
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

ntp4vc-write-case-def $a |- (
  NTP4VCWriteCase A B C D E F G H I
) <-> (
  (
    ( NTP4VCBounds A 0 )
    /\
    ( NTP4VCWritable A ) = 1
  )
  /\
  (
    NTP4VCAfterWrite A B C D E F G H I
  )
) $.

${
  $d o A B C D E F G $.

  ntp4vc-o3-continuation-def $a |- (
    NTP4VCO3Continuation A B C D E F G
  ) <-> (
    A. o e. { 0 , 1 }
      (
        (
          NTP4VCBoolResult
            ( NTP4VCPelts A ( NTP4VCOffset A ) )
            o
        )
        ->
        (
          (
            o = 1
            /\
            (
              NTP4VCWriteCase
                A B C D E F
                ( NTP4VCPelts A ( NTP4VCOffset A ) )
                1 G
            )
          )
          \/
          (
            o =/= 1
            /\
            (
              NTP4VCWriteCase
                A B C D E F
                ( NTP4VCPelts A ( NTP4VCOffset A ) )
                0 G
            )
          )
        )
      )
  ) $.
$}

${
  $d r A B C D E F $.

  ntp4vc-o2-true-def $a |- (
    NTP4VCO2True A B C D E F
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
          NTP4VCO3Continuation A B C D E r F
        )
      )
  ) $.
$}

${
  $d o A B C D E F G $.

  ntp4vc-o2-continuation-def $a |- (
    NTP4VCO2Continuation A B C D E F G
  ) <-> (
    A. o e. { 0 , 1 }
      (
        ( NTP4VCBoolResult B o )
        ->
        (
          (
            o = 1
            /\
            ( NTP4VCO2True A C D E F G )
          )
          \/
          (
            o =/= 1
            /\
            ( NTP4VCFinal C D E )
          )
        )
      )
  ) $.
$}

${
  $d p i l b q A B C D $.

  ntp4vc-continuation-def $a |- (
    NTP4VCContinuation A B C D
  ) <-> (
    ( NTP4VCInitialInvariant A B C )
    /\
    A. p e. ( NTP4VCPtr D )
      A. i e. NTP4VCWord32
        A. l e. NTP4VCWord64
          A. b e. NTP4VCWord64
            A. q e. ( NTP4VCPtr D )
              (
                ( NTP4VCSameMeta q B )
                ->
                (
                  (
                    NTP4VCLoopInvariant
                      p i l b q B C
                  )
                  ->
                  (
                    NTP4VCO2Continuation
                      p l q B C i D
                  )
                )
              )
  ) $.
$}

${
  $d p A B C $.

  ntp4vc-vc-def $a |- (
    NTP4VCVC A B C
  ) <-> (
    ( NTP4VCClosedBounds A 0 )
    /\
    A. p e. ( NTP4VCPtr C )
      (
        ( NTP4VCFullShift p A 0 )
        ->
        ( NTP4VCContinuation p A B C )
      )
  ) $.
$}

${
  $( Source parameters: A=x, B=sz, with common zone carrier Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-fact2 $e |- 0 <_ (
    ( NTP4VCValue A ( NTP4VCSigned32 B ) )
    -
    1
  ) $.
  ntp4vc-fact3 $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-decr-1-statement $a |- (
    NTP4VCVC A B Z
  ) $.
$}
