$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_incr_1qtvc: the verification
  condition for incrementing a writable multiprecision integer by one,
  including 32- and 64-bit word semantics, pointer bounds, carry
  propagation, memory updates and framing, and the final arithmetic
  relation.  This file contains no proof.

  Pointer values retain a total integer-indexed limb map with independent
  nonnegative length, integer offset and bounds, writability bit, and
  arbitrary nonempty zone.  The predicates below are definitional
  abbreviations for the source validity, value, pointer-copy, loop-invariant,
  update, branch, and postcondition formulas.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCPeltsMap
  NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCPeltsEq NTP4VCShiftCopy NTP4VCMetaEq
  NTP4VCTailFrame NTP4VCOutsideFrame NTP4VCInvariant NTP4VCFinal
  NTP4VCBoolResult NTP4VCGetBounds NTP4VCClosedBounds
  NTP4VCUpdateLaw NTP4VCWritePair NTP4VCNext NTP4VCAfterWrite
  NTP4VCStep NTP4VCLoopOutcome NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn $a wff NTP4VCInt32InBounds A $.
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
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-pelts-eq-syn $a wff NTP4VCPeltsEq A B $.
ntp4vc-shift-copy-syn $a wff NTP4VCShiftCopy A B C $.
ntp4vc-meta-eq-syn $a wff NTP4VCMetaEq A B $.
ntp4vc-tail-frame-syn $a wff NTP4VCTailFrame A B C D $.
ntp4vc-outside-frame-syn $a wff NTP4VCOutsideFrame A B C $.
ntp4vc-invariant-syn $a wff NTP4VCInvariant A B C D E F G $.
ntp4vc-final-syn $a wff NTP4VCFinal A B C $.
ntp4vc-bool-result-syn $a wff NTP4VCBoolResult A B $.
ntp4vc-get-bounds-syn $a wff NTP4VCGetBounds A $.
ntp4vc-closed-bounds-syn $a wff NTP4VCClosedBounds A B $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-write-pair-syn $a wff NTP4VCWritePair A B C $.
ntp4vc-next-syn $a wff NTP4VCNext A B C D E F G H $.
ntp4vc-after-write-syn $a wff NTP4VCAfterWrite A B C D E F G H $.
ntp4vc-step-syn $a wff NTP4VCStep A B C D E F $.
ntp4vc-loop-outcome-syn $a wff NTP4VCLoopOutcome A B C D E F G H $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C $.

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
        ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) ) )
$.

ntp4vc-data-def $a
  |- ( NTP4VCData A ) = ( 1st ` A )
$.

ntp4vc-length-def $a
  |- ( NTP4VCLength A ) = ( 2nd ` ( NTP4VCData A ) )
$.

ntp4vc-pelts-map-def $a
  |- ( NTP4VCPeltsMap A ) = ( 1st ` ( NTP4VCData A ) )
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
  |- ( NTP4VCPelts A B ) = ( ( NTP4VCPeltsMap A ) ` B )
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
  ntp4vc-pelts-eq-def $a
    |- ( NTP4VCPeltsEq A B <->
        A. j e. ZZ
          ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) )
  $.
$}

ntp4vc-shift-copy-def $a
  |- ( NTP4VCShiftCopy A B C <->
      ( ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C ) /\
        ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
          ( NTP4VCPeltsEq A B /\
            ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
              ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
                ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
                  ( ( NTP4VCZone A ) = ( NTP4VCZone B ) /\
                    ( NTP4VCWritable A ) =
                    ( NTP4VCWritable B ) ) ) ) ) ) ) ) )
$.

ntp4vc-meta-eq-def $a
  |- ( NTP4VCMetaEq A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

${
  $d j A B C D $.
  ntp4vc-tail-frame-def $a
    |- ( NTP4VCTailFrame A B C D <->
        A. j e. ZZ
          ( ( C <_ j /\ j < D ) ->
            ( NTP4VCPelts A ( ( NTP4VCOffset A ) + j ) ) =
            ( NTP4VCPelts B ( ( NTP4VCOffset A ) + j ) ) ) )
  $.
$}

${
  $d j A B C $.
  ntp4vc-outside-frame-def $a
    |- ( NTP4VCOutsideFrame A B C <->
        A. j e. ZZ
          ( ( j < ( NTP4VCOffset A ) \/
              ( ( NTP4VCOffset A ) + C ) <_ j ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

ntp4vc-invariant-def $a
  |- ( NTP4VCInvariant A B C D E F G <->
      ( ( 0 <_ ( NTP4VCSigned32 D ) /\
          ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 G ) ) /\
        ( ( D = G -> F =/= 0 ) /\
          ( ( NTP4VCOffset A ) =
              ( ( NTP4VCOffset B ) + ( NTP4VCSigned32 D ) ) /\
            ( NTP4VCPeltsEq A B /\
              ( ( NTP4VCLength A ) =
                  ( NTP4VCLength B ) /\
                ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
                  ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
                    ( ( F =/= 0 <-> E = 0 ) /\
                      ( ( 0 <_ E /\ E <_ 1 ) /\
                        ( ( NTP4VCWritable A ) = 1 /\
                          ( ( ( NTP4VCValue B
                                  ( NTP4VCSigned32 D ) ) +
                                ( ( ( 2 ^ ; 6 4 ) ^
                                      ( NTP4VCToNat
                                        ( NTP4VCSigned32 D ) ) ) x. E ) ) =
                              ( ( NTP4VCValue C
                                  ( NTP4VCSigned32 D ) ) + 1 ) /\
                            ( NTP4VCTailFrame B C
                                ( NTP4VCSigned32 D )
                                ( NTP4VCSigned32 G ) /\
                              NTP4VCOutsideFrame B C
                                ( NTP4VCSigned32 G ) ) ) ) ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C <->
      ( ( NTP4VCValue A ( NTP4VCSigned32 C ) ) =
          ( ( NTP4VCValue B ( NTP4VCSigned32 C ) ) + 1 ) /\
        NTP4VCOutsideFrame A B ( NTP4VCSigned32 C ) ) )
$.

ntp4vc-bool-result-def $a
  |- ( NTP4VCBoolResult A B <->
      ( ( A = 0 -> B = 1 ) /\ ( B = 1 -> A = 0 ) ) )
$.

ntp4vc-get-bounds-def $a
  |- ( NTP4VCGetBounds A <->
      ( ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) /\
        ( NTP4VCOffset A ) < ( NTP4VCMax A ) ) )
$.

ntp4vc-closed-bounds-def $a
  |- ( NTP4VCClosedBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) ) )
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

ntp4vc-write-pair-def $a
  |- ( NTP4VCWritePair A B C <->
      ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
        ( ( NTP4VCLength B ) = ( NTP4VCLength C ) /\
          ( ( NTP4VCOffset A ) = ( NTP4VCOffset C ) /\
            ( ( NTP4VCMin A ) = ( NTP4VCMin C ) /\
              ( ( NTP4VCMax A ) = ( NTP4VCMax C ) /\
                ( ( NTP4VCWritable A ) = ( NTP4VCWritable C ) /\
                  ( NTP4VCZone A ) = ( NTP4VCZone C ) ) ) ) ) ) ) )
$.

ntp4vc-next-def $a
  |- ( NTP4VCNext A B C D E F G H <->
      ( ( 0 <_ ( ( NTP4VCSigned32 G ) -
                  ( NTP4VCSigned32 D ) ) /\
          ( ( NTP4VCSigned32 G ) - ( NTP4VCSigned32 E ) ) <
          ( ( NTP4VCSigned32 G ) - ( NTP4VCSigned32 D ) ) ) /\
        NTP4VCInvariant A B C E H F G ) )
$.

${
  $d x y o z A B C D E F G H $.
  ntp4vc-after-write-def $a
    |- ( NTP4VCAfterWrite A B C D E F G H <->
        ( ( NTP4VCGetBounds A /\ ( NTP4VCWritable A ) = 1 ) /\
          A. x e. ( NTP4VCPtr H )
            A. y e. ( NTP4VCPtr H )
              ( NTP4VCWritePair x y A ->
                ( NTP4VCWritePair x y A ->
                  ( NTP4VCMetaEq y B ->
                    ( NTP4VCUpdateLaw A x
                        ( NTP4VCOffset x ) G ->
                      ( NTP4VCInt32InBounds
                          ( ( NTP4VCSigned32 D ) + 1 ) /\
                        A. o e. NTP4VCWord32
                          ( ( NTP4VCSigned32 o ) =
                              ( ( NTP4VCSigned32 D ) + 1 ) ->
                            ( NTP4VCClosedBounds x 1 /\
                              A. z e. ( NTP4VCPtr H )
                                ( NTP4VCShiftCopy z x 1 ->
                                  NTP4VCNext
                                    z y C D o G E F ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d r b A B C D E F $.
  ntp4vc-step-def $a
    |- ( NTP4VCStep A B C D E F <->
        ( NTP4VCGetBounds A /\
          A. r e. NTP4VCWord64
            ( r =
                ( ( ( NTP4VCPelts A ( NTP4VCOffset A ) ) + 1 )
                  mod ( 2 ^ ; 6 4 ) ) ->
              A. b e. { 0 , 1 }
                ( NTP4VCBoolResult r b ->
                  ( ( b = 1 /\
                      NTP4VCAfterWrite A B C D E 1 r F ) \/
                    ( b =/= 1 /\
                      NTP4VCAfterWrite A B C D E 0 r F ) ) ) ) ) )
  $.
$}

${
  $d b A B C D E F G H $.
  ntp4vc-loop-outcome-def $a
    |- ( NTP4VCLoopOutcome A B C D E F G H <->
        A. b e. { 0 , 1 }
          ( NTP4VCBoolResult F b ->
            ( ( b = 1 /\ NTP4VCStep A B C D G H ) \/
              ( b =/= 1 /\ NTP4VCFinal B C G ) ) ) )
  $.
$}

${
  $d o x i c r y A B C $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C <->
        ( NTP4VCClosedBounds A 0 /\
          A. o e. ( NTP4VCPtr C )
            ( NTP4VCShiftCopy o A 0 ->
              ( NTP4VCInvariant o A A 0 1 0 B /\
                A. x e. ( NTP4VCPtr C )
                  A. i e. NTP4VCWord32
                    A. c e. NTP4VCWord64
                      A. r e. NTP4VCWord64
                        A. y e. ( NTP4VCPtr C )
                          ( NTP4VCMetaEq y A ->
                            ( NTP4VCInvariant x y A i c r B ->
                              NTP4VCLoopOutcome
                                x y A i c r B C ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-valid-hyp $e |- NTP4VCValid A ( NTP4VCSigned32 B ) $.
  ntp4vc-positive-hyp $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-no-overflow-hyp $e
    |- ( ( NTP4VCValue A ( NTP4VCSigned32 B ) ) + 1 ) <
       ( ( 2 ^ ; 6 4 ) ^
         ( NTP4VCToNat ( NTP4VCSigned32 B ) ) )
  $.
  ntp4vc-writable-hyp $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-incr-1-statement $a
    |- NTP4VCVC A B Z
  $.
$}
