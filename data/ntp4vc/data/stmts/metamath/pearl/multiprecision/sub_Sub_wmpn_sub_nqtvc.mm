$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_sub_nqtvc: the verification condition for
  alias-aware equal-length multiprecision subtraction, including exact
  32- and 64-bit words, pointer validity and snapshots, borrow propagation,
  functional memory updates, loop invariants, framing, and the final
  arithmetic relation. This file contains no proof.

  Pointer data retains the source array's total integer-indexed limb map and
  independent nonnegative length, together with integer offset and bounds,
  writability, and an arbitrary nonempty zone. The predicates below are
  definitional abbreviations for the source snapshots, alias constraints,
  quantified transitions, update and frame conditions, loop branches, and
  complete verification condition. The proposition-valued conditional is
  rendered by the equivalent exhaustive guarded disjunction. The final $a is
  Metamath's native unproved statement encoding; there is no $p declaration.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSamePelts
  NTP4VCMapEqSub NTP4VCFrame NTP4VCNonoverlap
  NTP4VCInputSnapshot NTP4VCResultSnapshot NTP4VCSnapshots
  NTP4VCUpdateLaw NTP4VCWriteResult NTP4VCBounds
  NTP4VCBorrowBounds NTP4VCProgress NTP4VCValueEquation
  NTP4VCAliasState NTP4VCLoopInvariant NTP4VCFinal
  NTP4VCAfterWrite NTP4VCThenBranch NTP4VCLoopBody NTP4VCVC
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
ntp4vc-map-eq-sub-syn
  $a wff ( NTP4VCMapEqSub A B C D ) $.
ntp4vc-frame-syn $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-nonoverlap-syn
  $a wff ( NTP4VCNonoverlap A B C ) $.
ntp4vc-input-snapshot-syn
  $a wff ( NTP4VCInputSnapshot A B C ) $.
ntp4vc-result-snapshot-syn
  $a wff ( NTP4VCResultSnapshot A B ) $.
ntp4vc-snapshots-syn
  $a wff ( NTP4VCSnapshots A B C D E F ) $.
ntp4vc-update-law-syn
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-write-result-syn
  $a wff ( NTP4VCWriteResult A B C D ) $.
ntp4vc-bounds-syn $a wff ( NTP4VCBounds A B ) $.
ntp4vc-borrow-bounds-syn
  $a wff ( NTP4VCBorrowBounds A ) $.
ntp4vc-progress-syn $a wff ( NTP4VCProgress A B C ) $.
ntp4vc-value-equation-syn
  $a wff ( NTP4VCValueEquation A B C D E ) $.
ntp4vc-alias-state-syn
  $a wff ( NTP4VCAliasState A B C D E F ) $.
ntp4vc-loop-invariant-syn
  $a wff ( NTP4VCLoopInvariant A B C D E F G H I ) $.
ntp4vc-final-syn
  $a wff ( NTP4VCFinal A B C D E F G H ) $.
ntp4vc-after-write-syn
  $a wff ( NTP4VCAfterWrite A B C D E F G H I J K ) $.
ntp4vc-then-branch-syn
  $a wff ( NTP4VCThenBranch A B C D E F G H I J ) $.
ntp4vc-loop-body-syn
  $a wff ( NTP4VCLoopBody A B C D E F G H I J ) $.
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

${
  $d j A B $.

  ntp4vc-same-pelts-def $a |- (
    NTP4VCSamePelts A B
  ) <-> (
    A. j e. ZZ
      ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
  ) $.
$}

${
  $d j A B C D $.

  ntp4vc-map-eq-sub-def $a |- (
    NTP4VCMapEqSub A B C D
  ) <-> (
    A. j e. ZZ
      (
        (
          C <_ j
          /\
          j < D
        )
        ->
        ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
      )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-frame-def $a |- (
    NTP4VCFrame A B C
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

ntp4vc-nonoverlap-def $a |- (
  NTP4VCNonoverlap A B C
) <-> (
  ( NTP4VCOffset A ) = ( NTP4VCOffset B )
  \/
  (
    ( ( NTP4VCOffset A ) + C ) <_ ( NTP4VCOffset B )
    \/
    ( ( NTP4VCOffset B ) + C ) <_ ( NTP4VCOffset A )
  )
) $.

ntp4vc-input-snapshot-def $a |- (
  NTP4VCInputSnapshot A B C
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

ntp4vc-result-snapshot-def $a |- (
  NTP4VCResultSnapshot A B
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

ntp4vc-snapshots-def $a |- (
  NTP4VCSnapshots A B C D E F
) <-> (
  ( NTP4VCInputSnapshot A C D )
  /\
  (
    ( NTP4VCInputSnapshot B C E )
    /\
    ( NTP4VCResultSnapshot C F )
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

ntp4vc-write-result-def $a |- (
  NTP4VCWriteResult A B C D
) <-> (
  ( NTP4VCUpdateLaw A B C D )
  /\
  ( NTP4VCPelts B C ) = D
) $.

ntp4vc-bounds-def $a |- (
  NTP4VCBounds A B
) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A )
) $.

ntp4vc-borrow-bounds-def $a |- (
  NTP4VCBorrowBounds A
) <-> (
  0 <_ A
  /\
  A <_ 1
) $.

ntp4vc-progress-def $a |- (
  NTP4VCProgress A B C
) <-> (
  0 <_ (
    ( NTP4VCSigned32 A )
    -
    ( NTP4VCSigned32 B )
  )
  /\
  (
    ( NTP4VCSigned32 A )
    -
    ( NTP4VCSigned32 C )
  ) < (
    ( NTP4VCSigned32 A )
    -
    ( NTP4VCSigned32 B )
  )
) $.

ntp4vc-value-equation-def $a |- (
  NTP4VCValueEquation A B C D E
) <-> (
  (
    ( NTP4VCValue A D )
    -
    (
      ( NTP4VCRadix ^ ( NTP4VCToNat D ) )
      x.
      E
    )
  ) = (
    ( NTP4VCValue B D )
    -
    ( NTP4VCValue C D )
  )
) $.

ntp4vc-alias-state-def $a |- (
  NTP4VCAliasState A B C D E F
) <-> (
  ( NTP4VCSamePelts B A )
  /\
  (
    ( NTP4VCSamePelts A C )
    /\
    (
      (
        ( NTP4VCOffset A ) = ( NTP4VCOffset B )
        \/
        (
          NTP4VCMapEqSub
            B D
            ( NTP4VCOffset B )
            ( ( NTP4VCOffset B ) + F )
        )
      )
      /\
      (
        ( NTP4VCOffset A ) = ( NTP4VCOffset C )
        \/
        (
          NTP4VCMapEqSub
            C E
            ( NTP4VCOffset C )
            ( ( NTP4VCOffset C ) + F )
        )
      )
    )
  )
) $.

ntp4vc-loop-invariant-def $a |- (
  NTP4VCLoopInvariant A B C D E F G H I
) <-> (
  (
    0 <_ ( NTP4VCSigned32 E )
    /\
    ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 D )
  )
  /\
  (
    ( NTP4VCValueEquation I B C ( NTP4VCSigned32 E ) F )
    /\
    (
      ( NTP4VCFrame I A ( NTP4VCSigned32 E ) )
      /\
      (
        (
          NTP4VCAliasState
            I H G B C ( NTP4VCSigned32 D )
        )
        /\
        ( NTP4VCBorrowBounds F )
      )
    )
  )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D E F G H
) <-> (
  ( NTP4VCValueEquation H B C ( NTP4VCSigned32 D ) E )
  /\
  (
    ( NTP4VCBorrowBounds E )
    /\
    (
      ( NTP4VCFrame H A ( NTP4VCSigned32 D ) )
      /\
      (
        (
          ( NTP4VCOffset H ) = ( NTP4VCOffset G )
          \/
          (
            NTP4VCMapEqSub
              G B
              ( NTP4VCOffset G )
              (
                ( NTP4VCOffset G )
                +
                ( NTP4VCSigned32 D )
              )
          )
        )
        /\
        (
          ( NTP4VCOffset H ) = ( NTP4VCOffset F )
          \/
          (
            NTP4VCMapEqSub
              F C
              ( NTP4VCOffset F )
              (
                ( NTP4VCOffset F )
                +
                ( NTP4VCSigned32 D )
              )
          )
        )
      )
    )
  )
) $.

${
  $d y x r o A B C D E F G H I J K $.

  ntp4vc-after-write-def $a |- (
    NTP4VCAfterWrite A B C D E F G H I J K
  ) <-> (
    A. y e. ( NTP4VCPtr K )
      A. x e. ( NTP4VCPtr K )
        A. r e. ( NTP4VCPtr K )
          (
            ( NTP4VCSnapshots y x r G H I )
            ->
            (
              (
                NTP4VCWriteResult
                  I r
                  (
                    ( NTP4VCOffset r )
                    +
                    ( NTP4VCSigned32 E )
                  )
                  J
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
                      ( NTP4VCProgress D E o )
                      /\
                      (
                        NTP4VCLoopInvariant
                          A B C D o F y x r
                      )
                    )
                  )
              )
            )
          )
  ) $.
$}

${
  $d q c A B C D E F G H I J $.

  ntp4vc-then-branch-def $a |- (
    NTP4VCThenBranch A B C D E F G H I J
  ) <-> (
    ( NTP4VCBounds H ( NTP4VCSigned32 E ) )
    /\
    (
      ( NTP4VCBounds G ( NTP4VCSigned32 E ) )
      /\
      (
        ( NTP4VCBounds B ( NTP4VCSigned32 E ) )
        /\
        (
          ( NTP4VCBounds C ( NTP4VCSigned32 E ) )
          /\
          (
            ( NTP4VCBorrowBounds F )
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
                        NTP4VCPelts H
                          (
                            ( NTP4VCOffset H )
                            +
                            ( NTP4VCSigned32 E )
                          )
                      )
                      -
                      (
                        NTP4VCPelts G
                          (
                            ( NTP4VCOffset G )
                            +
                            ( NTP4VCSigned32 E )
                          )
                      )
                      -
                      F
                    )
                    /\
                    ( NTP4VCBorrowBounds c )
                  )
                  ->
                  (
                    (
                      ( NTP4VCBounds I ( NTP4VCSigned32 E ) )
                      /\
                      ( NTP4VCWritable I ) = 1
                    )
                    /\
                    (
                      NTP4VCAfterWrite
                        A B C D E c G H I q J
                    )
                  )
                )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-loop-body-def $a |- (
  NTP4VCLoopBody A B C D E F G H I J
) <-> (
  (
    (
      ( NTP4VCSigned32 E )
      <
      ( NTP4VCSigned32 D )
    )
    /\
    (
      NTP4VCThenBranch A B C D E F G H I J
    )
  )
  \/
  (
    (
      ( NTP4VCSigned32 D )
      <_
      ( NTP4VCSigned32 E )
    )
    /\
    (
      NTP4VCFinal A B C D F G H I
    )
  )
) $.

${
  $d i b y x r A B C D E $.

  ntp4vc-vc-def $a |- (
    NTP4VCVC A B C D E
  ) <-> (
    0 <_ 0
    /\
    (
      0 <_ ( NTP4VCSigned32 D )
      /\
      (
        ( NTP4VCValueEquation A B C 0 0 )
        /\
        (
          (
            NTP4VCAliasState
              A B C B C ( NTP4VCSigned32 D )
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
                  A. y e. ( NTP4VCPtr E )
                    A. x e. ( NTP4VCPtr E )
                      A. r e. ( NTP4VCPtr E )
                        (
                          ( NTP4VCSnapshots y x r C B A )
                          ->
                          (
                            (
                              NTP4VCLoopInvariant
                                A B C D i b y x r
                            )
                            ->
                            (
                              NTP4VCLoopBody
                                A B C D i b y x r E
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

${
  $( Source theorem parameters: A=r, B=x, C=y, D=sz, with zone Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sz-type $e |- D e. NTP4VCWord32 $.
  ntp4vc-r-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-x-type $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-nonnegative $e
    |- 0 <_ ( NTP4VCSigned32 D )
  $.
  ntp4vc-r-valid $e
    |- ( NTP4VCValid A ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-x-valid $e
    |- ( NTP4VCValid B ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-y-valid $e
    |- ( NTP4VCValid C ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-rx-nonoverlap $e
    |- ( NTP4VCNonoverlap A B ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-ry-nonoverlap $e
    |- ( NTP4VCNonoverlap A C ( NTP4VCSigned32 D ) )
  $.
  ntp4vc-rx-data $e |- ( NTP4VCData A ) = ( NTP4VCData B ) $.
  ntp4vc-xy-data $e |- ( NTP4VCData B ) = ( NTP4VCData C ) $.
  ntp4vc-r-writable $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-sub-n-statement $a
    |- ( NTP4VCVC A B C D Z )
  $.
$}
