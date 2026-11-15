$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_2qtvc: the verification condition
  for normalized two-limb multiprecision division, including reciprocal
  estimation, initial adjustment, loop-invariant preservation, quotient
  writes, and final remainder storage. This file contains no proof.

  Pointer data retains an arbitrary total ZZ-indexed map of 64-bit limbs and
  independent nonnegative-integer length metadata. Thus pelt lookup is total
  at every integer index and has no finite-sequence clamping or zero default.
  The remaining pointer fields are integer offset and bounds, a Boolean in
  the explicit two-element carrier { 0 , 1 }, and a value in an arbitrary
  nonempty zone.
  Integer arithmetic, order, truncated-negative-exponent power, and the
  positive-divisor Euclidean quotients are the standard SetMM operations.
  The helper predicates are definitional factorizations of the generated VC
  and retain its original universal and existential scopes.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCMapBase
  NTP4VCValueSub NTP4VCValue NTP4VCIPow NTP4VCValid NTP4VCMapEq
  NTP4VCUpdateLaw NTP4VCSameShape NTP4VCShiftCopy NTP4VCBounds
  NTP4VCInclusiveBounds NTP4VCReciprocal3 NTP4VCRemainder
  NTP4VCAdjustTest NTP4VCBorrowAll NTP4VCInitialAdjust NTP4VCLoopState
  NTP4VCFinalResult NTP4VCFinalX2All NTP4VCFinalX1All NTP4VCNextQ2All
  NTP4VCNextO7All NTP4VCDivResultAll NTP4VCShiftedWorkAll
  NTP4VCLoopStep NTP4VCLoopAll NTP4VCInitialResultAll NTP4VCDinvAll
  NTP4VCIndexAll NTP4VCLoadedWork NTP4VCWorkAll
  NTP4VCDisplacementAll
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
ntp4vc-map-base-syn $a class ( NTP4VCMapBase A ) $.
ntp4vc-value-sub-syn $a class ( NTP4VCValueSub A B C ) $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-ipow-syn $a class ( NTP4VCIPow A B ) $.
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-map-eq-syn $a wff NTP4VCMapEq A B $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-same-shape-syn $a wff NTP4VCSameShape A B $.
ntp4vc-shift-copy-syn $a wff NTP4VCShiftCopy A B C $.
ntp4vc-bounds-syn $a wff NTP4VCBounds A B $.
ntp4vc-inclusive-bounds-syn $a wff NTP4VCInclusiveBounds A B $.
ntp4vc-reciprocal3-syn $a wff NTP4VCReciprocal3 A B C $.
ntp4vc-remainder-syn $a wff NTP4VCRemainder A B C D $.
ntp4vc-adjust-test-syn $a wff NTP4VCAdjustTest A B C D $.
ntp4vc-borrow-all-syn $a wff NTP4VCBorrowAll A B $.
ntp4vc-initial-adjust-syn $a wff NTP4VCInitialAdjust A B C D E F G $.
ntp4vc-loop-state-syn $a wff NTP4VCLoopState A B C D E F G H I $.
ntp4vc-final-result-syn $a wff NTP4VCFinalResult A B C D E F $.
ntp4vc-final-x2-all-syn $a wff NTP4VCFinalX2All A B C D E F G H $.
ntp4vc-final-x1-all-syn $a wff NTP4VCFinalX1All A B C D E F G H $.
ntp4vc-next-q2-all-syn
  $a wff NTP4VCNextQ2All A B C D E F G H I J K L $.
ntp4vc-next-o7-all-syn
  $a wff NTP4VCNextO7All A B C D E F G H I J K $.
ntp4vc-div-result-all-syn
  $a wff NTP4VCDivResultAll A B C D E F G H I J K L M $.
ntp4vc-shifted-work-all-syn
  $a wff NTP4VCShiftedWorkAll A B C D E F G H I J K L M $.
ntp4vc-loop-step-syn
  $a wff NTP4VCLoopStep A B C D E F G H I J K L M $.
ntp4vc-loop-all-syn $a wff NTP4VCLoopAll A B C D E F G H I $.
ntp4vc-initial-result-all-syn
  $a wff NTP4VCInitialResultAll A B C D E F G H I J K L $.
ntp4vc-dinv-all-syn
  $a wff NTP4VCDinvAll A B C D E F G H I J K $.
ntp4vc-index-all-syn
  $a wff NTP4VCIndexAll A B C D E F G H I $.
ntp4vc-loaded-work-syn $a wff NTP4VCLoadedWork A B C D E F $.
ntp4vc-work-all-syn $a wff NTP4VCWorkAll A B C D E F $.
ntp4vc-displacement-all-syn
  $a wff NTP4VCDisplacementAll A B C D E $.

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

ntp4vc-map-base-def $a
  |- ( NTP4VCMapBase A ) = ( 1st ` ( NTP4VCData A ) )
$.

ntp4vc-pelts-def $a
  |- ( NTP4VCPelts A B ) = ( ( NTP4VCMapBase A ) ` B )
$.

${
  $d k A B C $.
  ntp4vc-value-sub-def $a
    |- ( NTP4VCValueSub A B C ) =
        sum_ k e. ( 0 ..^ ( NTP4VCToNat ( C - B ) ) )
          ( ( NTP4VCPelts A ( B + k ) ) x.
            ( ( 2 ^ ; 6 4 ) ^ k ) )
  $.
$}

ntp4vc-value-def $a
  |- ( NTP4VCValue A B ) =
      ( NTP4VCValueSub A ( NTP4VCOffset A )
        ( ( NTP4VCOffset A ) + B ) )
$.

ntp4vc-ipow-def $a
  |- ( NTP4VCIPow A B ) = ( A ^ ( NTP4VCToNat B ) )
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

ntp4vc-map-eq-def $a
  |- ( NTP4VCMapEq A B <->
      ( NTP4VCMapBase A ) = ( NTP4VCMapBase B ) )
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

ntp4vc-same-shape-def $a
  |- ( NTP4VCSameShape A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

ntp4vc-shift-copy-def $a
  |- ( NTP4VCShiftCopy A B C <->
      ( ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C ) /\
        ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
          ( NTP4VCMapEq A B /\
            ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
              ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
                ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
                  ( ( NTP4VCZone A ) = ( NTP4VCZone B ) /\
                    ( NTP4VCWritable A ) =
                    ( NTP4VCWritable B ) ) ) ) ) ) ) ) )
$.

ntp4vc-bounds-def $a
  |- ( NTP4VCBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A ) ) )
$.

ntp4vc-inclusive-bounds-def $a
  |- ( NTP4VCInclusiveBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) ) )
$.

ntp4vc-reciprocal3-def $a
  |- ( NTP4VCReciprocal3 A B C <->
      A =
      ( ( |_ ` (
          ( ( ( ( 2 ^ ; 6 4 ) x. ( 2 ^ ; 6 4 ) ) x.
                ( 2 ^ ; 6 4 ) ) - 1 )
          / ( C + ( ( 2 ^ ; 6 4 ) x. B ) ) ) ) -
        ( 2 ^ ; 6 4 ) ) )
$.

ntp4vc-remainder-def $a
  |- ( NTP4VCRemainder A B C D <->
      ( A + ( ( 2 ^ ; 6 4 ) x. B ) ) <
      ( C + ( ( 2 ^ ; 6 4 ) x. D ) ) )
$.

ntp4vc-adjust-test-def $a
  |- ( NTP4VCAdjustTest A B C D <->
      ( A < C \/ ( A = C /\ B <_ D ) ) )
$.

${
  $d d e A B $.
  ntp4vc-borrow-all-def $a
    |- ( NTP4VCBorrowAll A B <->
        A. d e. NTP4VCWord64
          A. e e. NTP4VCWord64
            ( ( ( d - ( ( 2 ^ ; 6 4 ) x. e ) ) =
                  ( ( A - B ) - 0 ) /\
                ( 0 <_ e /\ e <_ 1 ) ) ->
              ( 0 <_ e /\ e <_ 1 ) ) )
  $.
$}

${
  $d b d e A B C D E F G $.
  ntp4vc-initial-adjust-def $a
    |- ( NTP4VCInitialAdjust A B C D E F G <->
        E. b e. { 0 , 1 }
          ( ( ( b = 1 /\ NTP4VCAdjustTest D E F G ) \/
              ( b = 0 /\ -. NTP4VCAdjustTest D E F G ) ) /\
            ( ( b = 1 /\
                E. d e. NTP4VCWord64
                  ( ( B - ( ( 2 ^ ; 6 4 ) x. d ) ) =
                      ( ( G - E ) - 0 ) /\
                    ( ( 0 <_ d /\ d <_ 1 ) /\
                      E. e e. NTP4VCWord64
                        ( ( A - ( ( 2 ^ ; 6 4 ) x. e ) ) =
                            ( ( F - D ) - d ) /\
                          ( ( 0 <_ e /\ e <_ 1 ) /\ C = 1 ) ) ) ) ) \/
              ( b = 0 /\ ( ( A = F /\ B = G ) /\ C = 0 ) ) ) ) )
  $.
$}

ntp4vc-loop-state-def $a
  |- ( NTP4VCLoopState A B C D E F G H I <->
      ( ( ( 0 <_ I /\ I <_ ( ( NTP4VCSigned32 A ) - 2 ) ) /\
          ( ( NTP4VCOffset H ) = ( ( NTP4VCOffset B ) + I ) /\
            ( ( NTP4VCLength H ) = ( NTP4VCLength B ) /\
              ( ( NTP4VCMin H ) = ( NTP4VCMin B ) /\
                ( ( NTP4VCMax H ) = ( NTP4VCMax B ) /\
                  ( NTP4VCMapEq H B /\
                    ( ( NTP4VCWritable H ) = 1 /\
                      ( NTP4VCValue B ( NTP4VCSigned32 A ) ) =
                      ( ( ( ( NTP4VCValueSub D
                                  ( ( NTP4VCOffset D ) + I )
                                  ( ( ( NTP4VCOffset D ) +
                                      ( NTP4VCSigned32 A ) ) - 2 ) ) +
                                ( E x. ( NTP4VCIPow ( 2 ^ ; 6 4 )
                                  ( ( ( NTP4VCSigned32 A ) - 2 ) -
                                    I ) ) ) ) x.
                              ( NTP4VCValue C 2 ) ) x.
                            ( NTP4VCIPow ( 2 ^ ; 6 4 ) I ) ) +
                          ( ( NTP4VCValue B I ) +
                            ( ( NTP4VCIPow ( 2 ^ ; 6 4 ) I ) x.
                              ( F + ( ( 2 ^ ; 6 4 ) x. G ) ) ) ) )
                    ) ) ) ) ) ) ) /\
        NTP4VCRemainder F G
          ( NTP4VCPelts C ( NTP4VCOffset C ) )
          ( NTP4VCPelts C ( ( NTP4VCOffset C ) + 1 ) ) ) )
$.

ntp4vc-final-result-def $a
  |- ( NTP4VCFinalResult A B C D E F <->
      ( ( NTP4VCValue B ( NTP4VCSigned32 A ) ) =
        ( ( ( NTP4VCValue E ( ( NTP4VCSigned32 A ) - 2 ) ) +
              ( ( NTP4VCIPow ( 2 ^ ; 6 4 )
                    ( ( NTP4VCSigned32 A ) - 2 ) ) x. D ) ) x.
            ( NTP4VCValue C 2 ) ) +
          ( NTP4VCValue F 2 ) ) /\
        ( ( NTP4VCValue F 2 ) < ( NTP4VCValue C 2 ) /\
          ( 0 <_ D /\ D <_ 1 ) ) ) )
$.

${
  $d x A B C D E F G H $.
  ntp4vc-final-x2-all-def $a
    |- ( NTP4VCFinalX2All A B C D E F G H <->
        A. x e. ( NTP4VCPtr H )
          ( NTP4VCSameShape x F ->
            ( NTP4VCUpdateLaw F x ( NTP4VCOffset x ) G ->
              NTP4VCFinalResult A B C D E x ) ) )
  $.
$}

${
  $d x A B C D E F G H $.
  ntp4vc-final-x1-all-def $a
    |- ( NTP4VCFinalX1All A B C D E F G H <->
        A. x e. ( NTP4VCPtr H )
          ( NTP4VCSameShape x B ->
            ( ( NTP4VCUpdateLaw B x
                  ( ( NTP4VCOffset x ) + 1 ) G /\
                ( NTP4VCPelts x
                  ( ( NTP4VCOffset x ) + 1 ) ) = G ) ->
              ( ( NTP4VCBounds x 0 /\
                  ( NTP4VCWritable x ) = 1 ) /\
                NTP4VCFinalX2All A B C D E x F H ) ) ) )
  $.
$}

${
  $d x A B C D E F G H I J K L $.
  ntp4vc-next-q2-all-def $a
    |- ( NTP4VCNextQ2All A B C D E F G H I J K L <->
        A. x e. ( NTP4VCPtr L )
          ( NTP4VCSameShape x E ->
            ( ( NTP4VCUpdateLaw E x
                  ( ( NTP4VCOffset x ) + ( NTP4VCSigned32 H ) ) K /\
                ( NTP4VCPelts x
                  ( ( NTP4VCOffset x ) +
                    ( NTP4VCSigned32 H ) ) ) = K ) ->
              ( ( NTP4VCSigned32 H ) < ( NTP4VCSigned32 G ) /\
                NTP4VCLoopState A B C x D I J F
                  ( NTP4VCSigned32 H ) ) ) ) )
  $.
$}

${
  $d i A B C D E F G H I J K $.
  ntp4vc-next-o7-all-def $a
    |- ( NTP4VCNextO7All A B C D E F G H I J K <->
        A. i e. NTP4VCWord32
          ( ( NTP4VCSigned32 i ) =
              ( ( NTP4VCSigned32 G ) - 1 ) ->
            ( ( NTP4VCBounds E ( NTP4VCSigned32 i ) /\
                ( NTP4VCWritable E ) = 1 ) /\
              NTP4VCNextQ2All A B C D E F G i H I J K ) ) )
  $.
$}

${
  $d f g h A B C D E F G H I J K L M $.
  ntp4vc-div-result-all-def $a
    |- ( NTP4VCDivResultAll A B C D E F G H I J K L M <->
        A. f e. NTP4VCWord64
          A. g e. NTP4VCWord64
            A. h e. NTP4VCWord64
              ( ( ( ( ( ( ( f x. J ) +
                              ( ( 2 ^ ; 6 4 ) x. ( f x. I ) ) ) +
                            g ) +
                          ( ( 2 ^ ; 6 4 ) x. h ) ) =
                        ( ( NTP4VCPelts F ( NTP4VCOffset F ) ) +
                          ( ( 2 ^ ; 6 4 ) x. K ) ) +
                        ( ( ( 2 ^ ; 6 4 ) x. ( 2 ^ ; 6 4 ) ) x. L ) /\
                      0 <_ ( g + ( ( 2 ^ ; 6 4 ) x. h ) ) ) /\
                    ( g + ( ( 2 ^ ; 6 4 ) x. h ) ) <
                    ( J + ( ( 2 ^ ; 6 4 ) x. I ) ) ) ->
                ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 G ) - 1 ) /\
                  NTP4VCNextO7All A B C D E F G g h f M ) ) )
  $.
$}

${
  $d x A B C D E F G H I J K L M $.
  ntp4vc-shifted-work-all-def $a
    |- ( NTP4VCShiftedWorkAll A B C D E F G H I J K L M <->
        A. x e. ( NTP4VCPtr M )
          ( NTP4VCShiftCopy x F ( -u 1 ) ->
            ( NTP4VCBounds x 0 /\
              ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ I /\
                ( NTP4VCReciprocal3 H I J /\
                  ( NTP4VCRemainder K L J I /\
                    NTP4VCDivResultAll
                      A B C D E x G H I J K L M ) ) ) ) )
  $.
$}

ntp4vc-loop-step-def $a
  |- ( NTP4VCLoopStep A B C D E F G H I J K L M <->
      ( ( 0 < ( NTP4VCSigned32 G ) /\
          ( NTP4VCInclusiveBounds F ( -u 1 ) /\
            NTP4VCShiftedWorkAll
              A B C D E F G H I J K L M ) ) \/
        ( ( NTP4VCSigned32 G ) <_ 0 /\
          ( NTP4VCBounds B 1 /\
            ( ( NTP4VCWritable B ) = 1 /\
              NTP4VCFinalX1All A B C D E K L M ) ) ) ) )
$.

${
  $d i r s x y A B C D E F G H I $.
  ntp4vc-loop-all-def $a
    |- ( NTP4VCLoopAll A B C D E F G H I <->
        A. i e. NTP4VCWord32
          A. r e. NTP4VCWord64
            A. s e. NTP4VCWord64
              A. x e. ( NTP4VCPtr I )
                A. y e. ( NTP4VCPtr I )
                  ( NTP4VCSameShape y D ->
                    ( NTP4VCLoopState A B C y E r s x
                        ( NTP4VCSigned32 i ) ->
                      NTP4VCLoopStep
                        A B C E y x i F G H r s I ) ) )
  $.
$}

${
  $d d e f A B C D E F G H I J K L $.
  ntp4vc-initial-result-all-def $a
    |- ( NTP4VCInitialResultAll A B C D E F G H I J K L <->
        A. d e. NTP4VCWord64
          A. e e. NTP4VCWord64
            A. f e. NTP4VCWord64
              ( NTP4VCInitialAdjust d e f H I J K ->
                ( NTP4VCLoopState A B C D f e d E
                    ( NTP4VCSigned32 F ) /\
                  NTP4VCLoopAll A B C D f G H I L ) ) )
  $.
$}

${
  $d o A B C D E F G H I J K $.
  ntp4vc-dinv-all-def $a
    |- ( NTP4VCDinvAll A B C D E F G H I J K <->
        A. o e. NTP4VCWord64
          ( NTP4VCReciprocal3 o G H ->
            ( ( NTP4VCAdjustTest G H I J ->
                ( ( 0 <_ 0 /\ 0 <_ 1 ) /\
                  NTP4VCBorrowAll J H ) ) /\
              NTP4VCInitialResultAll
                A B C D E F o G H I J K ) ) )
  $.
$}

${
  $d i A B C D E F G H I $.
  ntp4vc-index-all-def $a
    |- ( NTP4VCIndexAll A B C D E F G H I <->
        A. i e. NTP4VCWord32
          ( ( NTP4VCSigned32 i ) =
              ( ( NTP4VCSigned32 A ) - 2 ) ->
            ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ F /\
              NTP4VCDinvAll A B C D E i F G H
                ( NTP4VCPelts E ( NTP4VCOffset E ) ) I ) ) )
  $.
$}

ntp4vc-loaded-work-def $a
  |- ( NTP4VCLoadedWork A B C D E F <->
      ( NTP4VCBounds C 1 /\
        ( NTP4VCBounds C 0 /\
          ( NTP4VCBounds E 1 /\
            ( NTP4VCBounds E 0 /\
              ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 A ) - 2 ) /\
                NTP4VCIndexAll A B C D E
                  ( NTP4VCPelts C ( ( NTP4VCOffset C ) + 1 ) )
                  ( NTP4VCPelts C ( NTP4VCOffset C ) )
                  ( NTP4VCPelts E ( ( NTP4VCOffset E ) + 1 ) )
                  F ) ) ) ) ) )
$.

${
  $d x A B C D E F $.
  ntp4vc-work-all-def $a
    |- ( NTP4VCWorkAll A B C D E F <->
        A. x e. ( NTP4VCPtr F )
          ( NTP4VCShiftCopy x B E ->
            NTP4VCLoadedWork A B C D x F ) )
  $.
$}

${
  $d i A B C D E $.
  ntp4vc-displacement-all-def $a
    |- ( NTP4VCDisplacementAll A B C D E <->
        A. i e. NTP4VCWord32
          ( ( NTP4VCSigned32 i ) =
              ( ( NTP4VCSigned32 A ) - 2 ) ->
            ( NTP4VCInclusiveBounds B ( NTP4VCSigned32 i ) /\
              NTP4VCWorkAll A B C D ( NTP4VCSigned32 i ) E ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sx-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-x-type $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-q-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-fact0 $e |- 2 <_ ( NTP4VCSigned32 A ) $.
  ntp4vc-fact1 $e |- NTP4VCValid B ( NTP4VCSigned32 A ) $.
  ntp4vc-fact2 $e |- NTP4VCValid C 2 $.
  ntp4vc-fact3 $e
    |- NTP4VCValid D ( ( NTP4VCSigned32 A ) - 2 )
  $.
  ntp4vc-fact4 $e
    |- ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_
       ( NTP4VCPelts C ( ( NTP4VCOffset C ) + 1 ) )
  $.
  ntp4vc-fact5 $e |- ( NTP4VCWritable D ) = 1 $.
  ntp4vc-fact6 $e |- ( NTP4VCWritable B ) = 1 $.

  ntp4vc-wmpn-divrem-2-statement $a
    |- ( NTP4VCInt32InBounds
            ( ( NTP4VCSigned32 A ) - 2 ) /\
         NTP4VCDisplacementAll A B C D Z )
  $.
$}
