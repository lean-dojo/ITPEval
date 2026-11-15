$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_subqtvc: the verification condition for
  unequal-length multiprecision subtraction, including exact 32- and 64-bit
  word semantics, pointer validity and aliasing, borrow propagation through two
  loops, memory updates and framing, and the final arithmetic relation. This
  file contains no proof.

  Pointer data retains the source array's total ZZ-indexed limb map and
  independent nonnegative length, together with integer offset and bounds,
  writability, and an arbitrary nonempty zone. The predicates below are
  definitional abbreviations for every snapshot, quantified transition,
  branch, loop invariant, update, and postcondition in the source VC.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCSamePelts NTP4VCMapEqSub NTP4VCFrame
  NTP4VCNonoverlap NTP4VCInputSnapshot NTP4VCResultSnapshot
  NTP4VCSnapshots NTP4VCUpdateLaw NTP4VCWriteResult NTP4VCBounds
  NTP4VCProgress NTP4VCLoopInvariant NTP4VCFirstInvariant
  NTP4VCSecondInvariant NTP4VCFinal
  NTP4VCSecondWrite NTP4VCSecondStep
  NTP4VCSecondBody NTP4VCSecondLoop
  NTP4VCO4Branch NTP4VCAfterIncrement NTP4VCFirstStep
  NTP4VCFirstBody NTP4VCFirstLoop
  NTP4VCBoolZero NTP4VCWmpnPost NTP4VCO2Branch
  NTP4VCContinuation NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn $a wff NTP4VCInt32InBounds A $.
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
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-same-pelts-syn $a wff NTP4VCSamePelts A B $.
ntp4vc-map-eq-sub-syn $a wff NTP4VCMapEqSub A B C D $.
ntp4vc-frame-syn $a wff NTP4VCFrame A B C $.
ntp4vc-nonoverlap-syn $a wff NTP4VCNonoverlap A B C D $.
ntp4vc-input-snapshot-syn
  $a wff NTP4VCInputSnapshot A B C $.
ntp4vc-result-snapshot-syn
  $a wff NTP4VCResultSnapshot A B $.
ntp4vc-snapshots-syn
  $a wff NTP4VCSnapshots A B C D E F $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-write-result-syn $a wff NTP4VCWriteResult A B C D $.
ntp4vc-bounds-syn $a wff NTP4VCBounds A B $.
ntp4vc-progress-syn $a wff NTP4VCProgress A B C $.
ntp4vc-loop-invariant-syn
  $a wff NTP4VCLoopInvariant A B C D E F G H I J $.
ntp4vc-first-invariant-syn
  $a wff NTP4VCFirstInvariant A B C D E F G H I J $.
ntp4vc-second-invariant-syn
  $a wff NTP4VCSecondInvariant A B C D E F G H I J $.
ntp4vc-final-syn
  $a wff NTP4VCFinal A B C D E F G H I $.
ntp4vc-second-write-syn
  $a wff NTP4VCSecondWrite A B C D E F G H I J $.
ntp4vc-second-step-syn
  $a wff NTP4VCSecondStep A B C D E F G H I J K $.
ntp4vc-second-body-syn
  $a wff NTP4VCSecondBody A B C D E F G H I J K $.
ntp4vc-second-loop-syn
  $a wff NTP4VCSecondLoop A B C D E F G H I J $.
ntp4vc-o4-branch-syn
  $a wff NTP4VCO4Branch A B C D E F G H I J K L M $.
ntp4vc-after-increment-syn
  $a wff NTP4VCAfterIncrement A B C D E F G H I J K L $.
ntp4vc-first-step-syn
  $a wff NTP4VCFirstStep A B C D E F G H I J K $.
ntp4vc-first-body-syn
  $a wff NTP4VCFirstBody A B C D E F G H I J K $.
ntp4vc-first-loop-syn
  $a wff NTP4VCFirstLoop A B C D E F G H I $.
ntp4vc-bool-zero-syn $a wff NTP4VCBoolZero A B $.
ntp4vc-wmpn-post-syn
  $a wff NTP4VCWmpnPost A B C D E F G H I $.
ntp4vc-o2-branch-syn
  $a wff NTP4VCO2Branch A B C D E F G H I J K $.
ntp4vc-continuation-syn
  $a wff NTP4VCContinuation A B C D E F G H I $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C D E F $.

ntp4vc-word32-def $a
  |- NTP4VCWord32 = ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) )
$.

ntp4vc-word64-def $a
  |- NTP4VCWord64 = ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) )
$.

ntp4vc-signed32-def $a
  |- ( NTP4VCSigned32 A ) =
      if ( A < ( 2 ^ ; 3 1 ) , A , ( A - ( 2 ^ ; 3 2 ) ) )
$.

ntp4vc-int32-in-bounds-def $a
  |- ( NTP4VCInt32InBounds A <->
      ( A e. ZZ /\
        ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) ) ) )
$.

ntp4vc-ptr-def $a
  |- ( NTP4VCPtr A ) =
      ( ( ( NTP4VCWord64 ^m ZZ ) X. NN0 ) X.
        ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) ) )
$.

ntp4vc-data-def $a
  |- ( NTP4VCData A ) = ( 1st ` A )
$.

ntp4vc-length-def $a
  |- ( NTP4VCLength A ) = ( 2nd ` ( NTP4VCData A ) )
$.

ntp4vc-offset-def $a
  |- ( NTP4VCOffset A ) = ( 1st ` ( 2nd ` A ) )
$.

ntp4vc-min-def $a
  |- ( NTP4VCMin A ) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
$.

ntp4vc-max-def $a
  |- ( NTP4VCMax A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
$.

ntp4vc-writable-def $a
  |- ( NTP4VCWritable A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
$.

ntp4vc-zone-def $a
  |- ( NTP4VCZone A ) =
      ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
$.

ntp4vc-to-nat-def $a
  |- ( NTP4VCToNat A ) = if ( 0 <_ A , A , 0 )
$.

ntp4vc-pelts-def $a
  |- ( NTP4VCPelts A B ) =
      ( ( 1st ` ( NTP4VCData A ) ) ` B )
$.

ntp4vc-valid-def $a
  |- ( NTP4VCValid A B <->
      ( NTP4VCInt32InBounds B /\
        ( 0 <_ B /\
          ( ( 0 <_ ( NTP4VCMin A ) /\
              ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) ) /\
            ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
              ( NTP4VCMax A ) <_ ( NTP4VCLength A ) ) ) ) ) )
$.

${
  $d k A B $.
  ntp4vc-value-def $a
    |- ( NTP4VCValue A B ) =
        sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
          ( ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) ) x.
            ( ( 2 ^ ; 6 4 ) ^ k ) )
  $.
$}

${
  $d j A B $.
  ntp4vc-same-pelts-def $a
    |- ( NTP4VCSamePelts A B <->
        A. j e. ZZ
          ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) )
  $.
$}

${
  $d j A B C D $.
  ntp4vc-map-eq-sub-def $a
    |- ( NTP4VCMapEqSub A B C D <->
        A. j e. ZZ
          ( ( C <_ j /\ j < D ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

${
  $d j A B C $.
  ntp4vc-frame-def $a
    |- ( NTP4VCFrame A B C <->
        A. j e. ZZ
          ( ( j < ( NTP4VCOffset A ) \/
              ( ( NTP4VCOffset A ) + C ) <_ j ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

ntp4vc-nonoverlap-def $a
  |- ( NTP4VCNonoverlap A B C D <->
      ( ( NTP4VCOffset A ) = ( NTP4VCOffset C ) \/
        ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCOffset C ) \/
          ( ( NTP4VCOffset C ) + D ) <_ ( NTP4VCOffset A ) ) ) )
$.

ntp4vc-input-snapshot-def $a
  |- ( NTP4VCInputSnapshot A B C <->
      ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
        ( ( NTP4VCLength B ) = ( NTP4VCLength C ) /\
          ( ( NTP4VCOffset A ) = ( NTP4VCOffset C ) /\
            ( ( NTP4VCMin A ) = ( NTP4VCMin C ) /\
              ( ( NTP4VCMax A ) = ( NTP4VCMax C ) /\
                ( ( NTP4VCWritable A ) = ( NTP4VCWritable C ) /\
                  ( NTP4VCZone A ) = ( NTP4VCZone C ) ) ) ) ) ) ) )
$.

ntp4vc-result-snapshot-def $a
  |- ( NTP4VCResultSnapshot A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

ntp4vc-snapshots-def $a
  |- ( NTP4VCSnapshots A B C D E F <->
      ( NTP4VCInputSnapshot A C D /\
        ( NTP4VCInputSnapshot B C E /\
          NTP4VCResultSnapshot C F ) ) )
$.

${
  $d j A B C D $.
  ntp4vc-update-law-def $a
    |- ( NTP4VCUpdateLaw A B C D <->
        A. j e. ZZ
          ( ( NTP4VCPelts B j ) =
            if ( j = C , D , ( NTP4VCPelts A j ) ) ) )
  $.
$}

ntp4vc-write-result-def $a
  |- ( NTP4VCWriteResult A B C D <->
      ( NTP4VCUpdateLaw A B C D /\
        ( NTP4VCPelts B C ) = D ) )
$.

ntp4vc-bounds-def $a
  |- ( NTP4VCBounds A B <->
      ( ( NTP4VCMin A ) <_ 
          ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) ) /\
        ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) ) <
          ( NTP4VCMax A ) ) )
$.

ntp4vc-progress-def $a
  |- ( NTP4VCProgress A B C <->
      ( 0 <_ ( ( NTP4VCSigned32 A ) - ( NTP4VCSigned32 B ) ) /\
        ( ( NTP4VCSigned32 A ) - ( NTP4VCSigned32 C ) ) <
        ( ( NTP4VCSigned32 A ) - ( NTP4VCSigned32 B ) ) ) )
$.

ntp4vc-loop-invariant-def $a
  |- ( NTP4VCLoopInvariant A B C D E F G H I J <->
      ( ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 I ) /\
        ( ( NTP4VCSigned32 I ) <_ ( NTP4VCSigned32 B ) /\
          ( ( ( NTP4VCValue F ( NTP4VCSigned32 I ) ) -
              ( ( ( 2 ^ ; 6 4 ) ^
                  ( NTP4VCToNat ( NTP4VCSigned32 I ) ) ) x. J ) ) =
              ( ( NTP4VCValue D ( NTP4VCSigned32 I ) ) -
                ( NTP4VCValue E ( NTP4VCSigned32 A ) ) ) /\
            ( NTP4VCFrame F C ( NTP4VCSigned32 I ) /\
              ( NTP4VCSamePelts G F /\
                ( NTP4VCSamePelts H F /\
                  ( ( ( NTP4VCOffset F ) = ( NTP4VCOffset G ) \/
                      NTP4VCMapEqSub G D
                        ( NTP4VCOffset G )
                        ( ( NTP4VCOffset G ) +
                          ( NTP4VCSigned32 B ) ) ) /\
                    ( ( ( NTP4VCOffset F ) =
                          ( NTP4VCOffset H ) \/
                        NTP4VCMapEqSub H E
                          ( NTP4VCOffset H )
                          ( ( NTP4VCOffset H ) +
                            ( NTP4VCSigned32 A ) ) ) /\
                      ( 0 <_ J /\ J <_ 1 ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-first-invariant-def $a
  |- ( NTP4VCFirstInvariant A B C D E F G H I J <->
      ( NTP4VCLoopInvariant A B C D E F G H I J /\
        ( I = B \/ J = 1 ) ) )
$.

ntp4vc-second-invariant-def $a
  |- ( NTP4VCSecondInvariant A B C D E F G H I J <->
      ( NTP4VCLoopInvariant A B C D E F G H I J /\
        ( I = B \/ J = 0 ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C D E F G H I <->
      ( ( ( NTP4VCValue F ( NTP4VCSigned32 B ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 B ) ) ) x. I ) ) =
          ( ( NTP4VCValue D ( NTP4VCSigned32 B ) ) -
            ( NTP4VCValue E ( NTP4VCSigned32 A ) ) ) /\
        ( ( 0 <_ I /\ I <_ 1 ) /\
          ( NTP4VCFrame F C ( NTP4VCSigned32 B ) /\
            ( ( ( NTP4VCOffset F ) = ( NTP4VCOffset G ) \/
                NTP4VCMapEqSub G D
                  ( NTP4VCOffset G )
                  ( ( NTP4VCOffset G ) +
                    ( NTP4VCSigned32 B ) ) ) /\
              ( ( NTP4VCOffset F ) = ( NTP4VCOffset H ) \/
                NTP4VCMapEqSub H E
                  ( NTP4VCOffset H )
                  ( ( NTP4VCOffset H ) +
                    ( NTP4VCSigned32 A ) ) ) ) ) ) ) )
$.

${
  $d o A B C D E F G H I J $.
  ntp4vc-second-write-def $a
    |- ( NTP4VCSecondWrite A B C D E F G H I J <->
        ( NTP4VCInt32InBounds
            ( ( NTP4VCSigned32 F ) + 1 ) /\
          A. o e. NTP4VCWord32
            ( ( NTP4VCSigned32 o ) =
                ( ( NTP4VCSigned32 F ) + 1 ) ->
              ( NTP4VCProgress B F o /\
                NTP4VCSecondInvariant
                  A B C D E J I H o G ) ) ) )
  $.
$}

${
  $d p q s A B C D E F G H I J K $.
  ntp4vc-second-step-def $a
    |- ( NTP4VCSecondStep A B C D E F G H I J K <->
        ( NTP4VCBounds H F /\
          ( NTP4VCBounds D F /\
            ( ( NTP4VCBounds J F /\
                ( NTP4VCWritable J ) = 1 ) /\
              A. p e. ( NTP4VCPtr K )
                A. q e. ( NTP4VCPtr K )
                  A. s e. ( NTP4VCPtr K )
                    ( NTP4VCSnapshots p q s G H J ->
                      ( NTP4VCWriteResult J s
                          ( ( NTP4VCOffset s ) +
                            ( NTP4VCSigned32 F ) )
                          ( NTP4VCPelts H
                            ( ( NTP4VCOffset H ) +
                              ( NTP4VCSigned32 F ) ) ) ->
                        NTP4VCSecondWrite
                          A B C D E F I p q s ) ) ) ) ) )
  $.
$}

ntp4vc-second-body-def $a
  |- ( NTP4VCSecondBody A B C D E F G H I J K <->
      ( ( ( NTP4VCSigned32 F ) < ( NTP4VCSigned32 B ) /\
          NTP4VCSecondStep A B C D E F G H I J K ) \/
        ( ( NTP4VCSigned32 B ) <_ ( NTP4VCSigned32 F ) /\
          NTP4VCFinal A B C D E J H G I ) ) )
$.

${
  $d i p q s A B C D E F G H I J $.
  ntp4vc-second-loop-def $a
    |- ( NTP4VCSecondLoop A B C D E F G H I J <->
        A. i e. NTP4VCWord32
          A. p e. ( NTP4VCPtr J )
            A. q e. ( NTP4VCPtr J )
              A. s e. ( NTP4VCPtr J )
                ( NTP4VCSnapshots p q s F G H ->
                  ( NTP4VCSecondInvariant
                      A B C D E s q p i I ->
                    NTP4VCSecondBody
                      A B C D E i p q I s J ) ) ) )
  $.
$}

ntp4vc-o4-branch-def $a
  |- ( NTP4VCO4Branch A B C D E F G H I J K L M <->
      ( ( L =/= 1 /\
          ( NTP4VCSecondInvariant
              A B C D E J I H K 0 /\
            NTP4VCSecondLoop
              A B C D E H I J 0 M ) ) \/
        ( L = 1 /\
          ( NTP4VCProgress B F K /\
            NTP4VCFirstInvariant
              A B C D E J I H K G ) ) ) )
$.

${
  $d p q s o b A B C D E F G H I J K L $.
  ntp4vc-after-increment-def $a
    |- ( NTP4VCAfterIncrement A B C D E F G H I J K L <->
        A. p e. ( NTP4VCPtr L )
          A. q e. ( NTP4VCPtr L )
            A. s e. ( NTP4VCPtr L )
              ( NTP4VCSnapshots p q s H I J ->
                ( NTP4VCWriteResult J s
                    ( ( NTP4VCOffset s ) +
                      ( NTP4VCSigned32 F ) ) K ->
                  ( NTP4VCInt32InBounds
                      ( ( NTP4VCSigned32 F ) + 1 ) /\
                    A. o e. NTP4VCWord32
                      ( ( NTP4VCSigned32 o ) =
                          ( ( NTP4VCSigned32 F ) + 1 ) ->
                        A. b e. 2
                          ( NTP4VCBoolZero
                              ( NTP4VCPelts I
                                ( ( NTP4VCOffset I ) +
                                  ( NTP4VCSigned32 F ) ) ) b ->
                            NTP4VCO4Branch
                              A B C D E F G p q s o b L ) ) ) ) ) )
  $.
$}

${
  $d v A B C D E F G H I J K $.
  ntp4vc-first-step-def $a
    |- ( NTP4VCFirstStep A B C D E F G H I J K <->
        ( NTP4VCBounds I F /\
          ( NTP4VCBounds D F /\
            A. v e. NTP4VCWord64
              ( v =
                  ( ( ( NTP4VCPelts I
                          ( ( NTP4VCOffset I ) +
                            ( NTP4VCSigned32 F ) ) ) - 1 )
                    mod ( 2 ^ ; 6 4 ) ) ->
                ( ( NTP4VCBounds J F /\
                    ( NTP4VCWritable J ) = 1 ) /\
                  NTP4VCAfterIncrement
                    A B C D E F G H I J v K ) ) ) ) )
  $.
$}

ntp4vc-first-body-def $a
  |- ( NTP4VCFirstBody A B C D E F G H I J K <->
      ( ( ( NTP4VCSigned32 F ) < ( NTP4VCSigned32 B ) /\
          NTP4VCFirstStep A B C D E F G H I J K ) \/
        ( ( NTP4VCSigned32 B ) <_ ( NTP4VCSigned32 F ) /\
          ( NTP4VCSecondInvariant
              A B C D E J I H F G /\
            NTP4VCSecondLoop
              A B C D E H I J G K ) ) ) )
$.

${
  $d i c p q s A B C D E F G H I $.
  ntp4vc-first-loop-def $a
    |- ( NTP4VCFirstLoop A B C D E F G H I <->
        A. i e. NTP4VCWord32
          A. c e. NTP4VCWord64
            A. p e. ( NTP4VCPtr I )
              A. q e. ( NTP4VCPtr I )
                A. s e. ( NTP4VCPtr I )
                  ( NTP4VCSnapshots p q s F G H ->
                    ( NTP4VCFirstInvariant
                        A B C D E s q p i c ->
                      NTP4VCFirstBody
                        A B C D E i c p q s I ) ) ) )
  $.
$}

ntp4vc-bool-zero-def $a
  |- ( NTP4VCBoolZero A B <->
      ( ( A = 0 -> B = 1 ) /\ ( B = 1 -> A = 0 ) ) )
$.

ntp4vc-wmpn-post-def $a
  |- ( NTP4VCWmpnPost A B C D E F G H I <->
      ( ( ( NTP4VCValue F ( NTP4VCSigned32 A ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 A ) ) ) x. I ) ) =
          ( ( NTP4VCValue D ( NTP4VCSigned32 A ) ) -
            ( NTP4VCValue E ( NTP4VCSigned32 A ) ) ) /\
        ( ( 0 <_ I /\ I <_ 1 ) /\
          ( NTP4VCFrame F C ( NTP4VCSigned32 A ) /\
            ( ( ( NTP4VCOffset F ) = ( NTP4VCOffset G ) \/
                NTP4VCMapEqSub G D
                  ( NTP4VCOffset G )
                  ( ( NTP4VCOffset G ) +
                    ( NTP4VCSigned32 A ) ) ) /\
              ( ( NTP4VCOffset F ) = ( NTP4VCOffset H ) \/
                NTP4VCMapEqSub H E
                  ( NTP4VCOffset H )
                  ( ( NTP4VCOffset H ) +
                    ( NTP4VCSigned32 A ) ) ) ) ) ) ) )
$.

ntp4vc-o2-branch-def $a
  |- ( NTP4VCO2Branch A B C D E F G H I J K <->
      ( ( J =/= 1 /\
          ( NTP4VCFirstInvariant
              A B C D E H G F A I /\
            NTP4VCFirstLoop
              A B C D E F G H K ) ) \/
        ( J = 1 /\
          ( NTP4VCSecondInvariant
              A B C D E H G F A I /\
            NTP4VCSecondLoop
              A B C D E F G H I K ) ) ) )
$.

${
  $d o b A B C D E F G H I $.
  ntp4vc-continuation-def $a
    |- ( NTP4VCContinuation A B C D E F G H I <->
        A. o e. NTP4VCWord64
          ( NTP4VCWmpnPost A B C D E H G F o ->
            A. b e. 2
              ( NTP4VCBoolZero o b ->
                NTP4VCO2Branch
                  A B C D E F G H o b I ) ) ) )
  $.
$}

${
  $d p q s A B C D E F $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D E F <->
        ( 0 <_ ( NTP4VCSigned32 A ) /\
          ( NTP4VCValid C ( NTP4VCSigned32 A ) /\
            ( NTP4VCValid D ( NTP4VCSigned32 A ) /\
              ( NTP4VCValid E ( NTP4VCSigned32 A ) /\
                ( NTP4VCNonoverlap
                    C ( NTP4VCSigned32 A )
                    D ( NTP4VCSigned32 A ) /\
                  ( NTP4VCNonoverlap
                      C ( NTP4VCSigned32 A )
                      E ( NTP4VCSigned32 A ) /\
                    ( ( NTP4VCData C ) = ( NTP4VCData D ) /\
                      ( ( NTP4VCData D ) = ( NTP4VCData E ) /\
                        ( ( NTP4VCWritable C ) = 1 /\
                          A. p e. ( NTP4VCPtr F )
                            A. q e. ( NTP4VCPtr F )
                              A. s e. ( NTP4VCPtr F )
                                ( NTP4VCSnapshots p q s E D C ->
                                  NTP4VCContinuation
                                    A B C D E p q s F ) ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sy-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-r-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-x-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- E e. ( NTP4VCPtr Z ) $.
  ntp4vc-sy-nonnegative $e
    |- 0 <_ ( NTP4VCSigned32 A )
  $.
  ntp4vc-size-order $e
    |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B )
  $.
  ntp4vc-r-valid $e
    |- NTP4VCValid C ( NTP4VCSigned32 B )
  $.
  ntp4vc-x-valid $e
    |- NTP4VCValid D ( NTP4VCSigned32 B )
  $.
  ntp4vc-y-valid $e
    |- NTP4VCValid E ( NTP4VCSigned32 A )
  $.
  ntp4vc-rx-nonoverlap $e
    |- NTP4VCNonoverlap
        C ( NTP4VCSigned32 B ) D ( NTP4VCSigned32 B )
  $.
  ntp4vc-ry-nonoverlap $e
    |- NTP4VCNonoverlap
        C ( NTP4VCSigned32 B ) E ( NTP4VCSigned32 A )
  $.
  ntp4vc-rx-data $e
    |- ( NTP4VCData C ) = ( NTP4VCData D )
  $.
  ntp4vc-xy-data $e
    |- ( NTP4VCData D ) = ( NTP4VCData E )
  $.
  ntp4vc-r-writable $e
    |- ( NTP4VCWritable C ) = 1
  $.

  ntp4vc-wmpn-sub-statement $a
    |- NTP4VCVC A B C D E Z
  $.
$}
