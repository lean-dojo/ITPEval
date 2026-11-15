$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_subqtvc: the verification condition for
  possibly unequal-length multiprecision subtraction into a separate
  destination,
  including pointer alias separation, borrow arithmetic, memory framing, and
  preservation of operand values and pointer metadata. This file contains no
  proof.

  The source 32- and 64-bit words are their exact unsigned integer ranges.
  Signed two's-complement interpretation is retained for the 32-bit size
  parameters, while 64-bit limbs remain unsigned.
  A pointer contains the source array's total ZZ-indexed limb map and
  independent nonnegative length, together with integer offset and bounds,
  writability, and an arbitrary nonempty zone. Alias memories retain all
  source record fields. The predicates below are definitional abbreviations
  for every nested quantifier, implication, asymmetric size condition, alias
  condition, arithmetic postcondition, and frame condition in the original
  verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCAliasMem
  NTP4VCData NTP4VCLength NTP4VCPlength NTP4VCOffset NTP4VCMin
  NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCPelts
  NTP4VCZr NTP4VCZx NTP4VCZy NTP4VCMr NTP4VCMx NTP4VCMy
  NTP4VCLr NTP4VCLx NTP4VCLy NTP4VCOk
  NTP4VCToNat NTP4VCValid NTP4VCValue NTP4VCSamePelts
  NTP4VCMapEqSub NTP4VCMapEqSubShift NTP4VCFrame
  NTP4VCViewEq NTP4VCViewMinEq NTP4VCNonoverlap
  NTP4VCOrderedTriple NTP4VCSameAliasFields
  NTP4VCSnapshot NTP4VCNrSnapshot NTP4VCWmpnPost
  NTP4VCClosePre NTP4VCFinalPost NTP4VCCloseTransition
  NTP4VCCloseObligation NTP4VCAfterWmpnSub
  NTP4VCOpenedCore NTP4VCOpenSepAntecedent NTP4VCOpenedState
  NTP4VCAllOpenedStates NTP4VCAllViews NTP4VCSubConclusion
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn $a wff NTP4VCInt32InBounds A $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-alias-mem-syn $a class ( NTP4VCAliasMem A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
ntp4vc-plength-syn $a class ( NTP4VCPlength A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-zr-syn $a class ( NTP4VCZr A ) $.
ntp4vc-zx-syn $a class ( NTP4VCZx A ) $.
ntp4vc-zy-syn $a class ( NTP4VCZy A ) $.
ntp4vc-mr-syn $a class ( NTP4VCMr A ) $.
ntp4vc-mx-syn $a class ( NTP4VCMx A ) $.
ntp4vc-my-syn $a class ( NTP4VCMy A ) $.
ntp4vc-lr-syn $a class ( NTP4VCLr A ) $.
ntp4vc-lx-syn $a class ( NTP4VCLx A ) $.
ntp4vc-ly-syn $a class ( NTP4VCLy A ) $.
ntp4vc-ok-syn $a class ( NTP4VCOk A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-same-pelts-syn $a wff NTP4VCSamePelts A B $.
ntp4vc-map-eq-sub-syn $a wff NTP4VCMapEqSub A B C D $.
ntp4vc-map-eq-sub-shift-syn
  $a wff NTP4VCMapEqSubShift A B C D E $.
ntp4vc-frame-syn $a wff NTP4VCFrame A B C $.
ntp4vc-view-eq-syn $a wff NTP4VCViewEq A B $.
ntp4vc-view-min-eq-syn $a wff NTP4VCViewMinEq A B $.
ntp4vc-nonoverlap-syn $a wff NTP4VCNonoverlap A B C D $.
ntp4vc-ordered-triple-syn $a wff NTP4VCOrderedTriple A B C D $.
ntp4vc-same-alias-fields-syn
  $a wff NTP4VCSameAliasFields A B $.
ntp4vc-snapshot-syn $a wff NTP4VCSnapshot A B C $.
ntp4vc-nr-snapshot-syn $a wff NTP4VCNrSnapshot A B $.
ntp4vc-wmpn-post-syn
  $a wff NTP4VCWmpnPost A B C D E F G H I $.
ntp4vc-close-pre-syn
  $a wff NTP4VCClosePre A B C D E F G H I $.
ntp4vc-final-post-syn
  $a wff NTP4VCFinalPost A B C D E F G H I $.
ntp4vc-close-transition-syn
  $a wff NTP4VCCloseTransition A B C D E F G H I J K L M N O $.
ntp4vc-close-obligation-syn
  $a wff NTP4VCCloseObligation A B C D E F G H I J K L M N $.
ntp4vc-after-wmpn-sub-syn
  $a wff NTP4VCAfterWmpnSub A B C D E F G H I J K L M $.
ntp4vc-opened-core-syn
  $a wff NTP4VCOpenedCore A B C D E $.
ntp4vc-open-sep-antecedent-syn
  $a wff NTP4VCOpenSepAntecedent A B C D E F G H I J K L $.
ntp4vc-opened-state-syn
  $a wff NTP4VCOpenedState A B C D E F G H I J K L M $.
ntp4vc-all-opened-states-syn
  $a wff NTP4VCAllOpenedStates A B C D E F G H I $.
ntp4vc-all-views-syn
  $a wff NTP4VCAllViews A B C D E F $.
ntp4vc-sub-conclusion-syn
  $a wff NTP4VCSubConclusion A B C D E F $.

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

ntp4vc-alias-mem-def $a
  |- ( NTP4VCAliasMem A ) =
      ( A X.
        ( A X.
          ( A X.
            ( NTP4VCWord32 X.
              ( NTP4VCWord32 X.
                ( NTP4VCWord32 X.
                  ( NTP4VCWord32 X.
                    ( NTP4VCWord32 X.
                      ( NTP4VCWord32 X. 2 ) ) ) ) ) ) ) ) )
$.

ntp4vc-data-def $a
  |- ( NTP4VCData A ) = ( 1st ` A )
$.

ntp4vc-length-def $a
  |- ( NTP4VCLength A ) = ( 2nd ` ( NTP4VCData A ) )
$.

ntp4vc-plength-def $a
  |- ( NTP4VCPlength A ) = ( NTP4VCLength A )
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

ntp4vc-pelts-def $a
  |- ( NTP4VCPelts A B ) =
      ( ( 1st ` ( NTP4VCData A ) ) ` B )
$.

ntp4vc-zr-def $a |- ( NTP4VCZr A ) = ( 1st ` A ) $.
ntp4vc-zx-def $a |- ( NTP4VCZx A ) = ( 1st ` ( 2nd ` A ) ) $.
ntp4vc-zy-def $a
  |- ( NTP4VCZy A ) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
$.
ntp4vc-mr-def $a
  |- ( NTP4VCMr A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
$.
ntp4vc-mx-def $a
  |- ( NTP4VCMx A ) =
      ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) )
$.
ntp4vc-my-def $a
  |- ( NTP4VCMy A ) =
      ( 1st `
        ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
$.
ntp4vc-lr-def $a
  |- ( NTP4VCLr A ) =
      ( 1st `
        ( 2nd `
          ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) ) )
$.
ntp4vc-lx-def $a
  |- ( NTP4VCLx A ) =
      ( 1st `
        ( 2nd `
          ( 2nd `
            ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) ) ) )
$.
ntp4vc-ly-def $a
  |- ( NTP4VCLy A ) =
      ( 1st `
        ( 2nd `
          ( 2nd `
            ( 2nd `
              ( 2nd `
                ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) ) ) ) )
$.
ntp4vc-ok-def $a
  |- ( NTP4VCOk A ) =
      ( 2nd `
        ( 2nd `
          ( 2nd `
            ( 2nd `
              ( 2nd `
                ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) ) ) ) )
$.

ntp4vc-to-nat-def $a
  |- ( NTP4VCToNat A ) = if ( 0 <_ A , A , 0 )
$.

ntp4vc-valid-def $a
  |- ( NTP4VCValid A B <->
      ( NTP4VCInt32InBounds B /\
        ( 0 <_ B /\
          ( ( 0 <_ ( NTP4VCMin A ) /\
              ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) ) /\
            ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
              ( NTP4VCMax A ) <_ ( NTP4VCPlength A ) ) ) ) ) )
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
  $d j A B C D E $.
  ntp4vc-map-eq-sub-shift-def $a
    |- ( NTP4VCMapEqSubShift A B C D E <->
        A. j e. ZZ
          ( ( 0 <_ j /\ j < E ) ->
            ( NTP4VCPelts A ( C + j ) ) =
            ( NTP4VCPelts B ( D + j ) ) ) )
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

ntp4vc-view-eq-def $a
  |- ( NTP4VCViewEq A B <->
      ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
        ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
          ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) )
$.

ntp4vc-view-min-eq-def $a
  |- ( NTP4VCViewMinEq A B <->
      ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
        ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
          ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
            ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) )
$.

ntp4vc-nonoverlap-def $a
  |- ( NTP4VCNonoverlap A B C D <->
      ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) \/
        ( ( ( NTP4VCOffset A ) + C ) <_ ( NTP4VCOffset B ) \/
          ( ( NTP4VCOffset B ) + D ) <_ ( NTP4VCOffset A ) ) ) )
$.

ntp4vc-ordered-triple-def $a
  |- ( NTP4VCOrderedTriple A B C D <->
      ( 0 <_ ( NTP4VCOffset A ) /\
        ( ( ( NTP4VCOffset A ) + D ) <_ ( NTP4VCOffset B ) /\
          ( ( NTP4VCOffset B ) + D ) <_ ( NTP4VCOffset C ) ) ) )
$.

ntp4vc-same-alias-fields-def $a
  |- ( NTP4VCSameAliasFields A B <->
      ( ( NTP4VCZr A ) = ( NTP4VCZr B ) /\
        ( ( NTP4VCZx A ) = ( NTP4VCZx B ) /\
          ( ( NTP4VCZy A ) = ( NTP4VCZy B ) /\
            ( ( NTP4VCMr A ) = ( NTP4VCMr B ) /\
              ( ( NTP4VCMx A ) = ( NTP4VCMx B ) /\
                ( ( NTP4VCMy A ) = ( NTP4VCMy B ) /\
                  ( ( NTP4VCLr A ) = ( NTP4VCLr B ) /\
                    ( ( NTP4VCLx A ) = ( NTP4VCLx B ) /\
                      ( NTP4VCLy A ) = ( NTP4VCLy B ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-snapshot-def $a
  |- ( NTP4VCSnapshot A B C <->
      ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
        ( ( NTP4VCLength B ) = ( NTP4VCLength C ) /\
          ( ( NTP4VCOffset A ) = ( NTP4VCOffset C ) /\
            ( ( NTP4VCMin A ) = ( NTP4VCMin C ) /\
              ( ( NTP4VCMax A ) = ( NTP4VCMax C ) /\
                ( ( NTP4VCWritable A ) = ( NTP4VCWritable C ) /\
                  ( NTP4VCZone A ) = ( NTP4VCZone C ) ) ) ) ) ) ) )
$.

ntp4vc-nr-snapshot-def $a
  |- ( NTP4VCNrSnapshot A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

ntp4vc-wmpn-post-def $a
  |- ( NTP4VCWmpnPost A B C D E F G H I <->
      ( ( ( NTP4VCValue D ( NTP4VCSigned32 B ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 B ) ) ) x. I ) ) =
        ( ( NTP4VCValue E ( NTP4VCSigned32 B ) ) -
          ( NTP4VCValue F ( NTP4VCSigned32 A ) ) ) /\
        ( ( 0 <_ I /\ I <_ 1 ) /\
          ( NTP4VCFrame D C ( NTP4VCSigned32 B ) /\
            ( ( ( NTP4VCOffset D ) = ( NTP4VCOffset G ) \/
                NTP4VCMapEqSub G E
                  ( NTP4VCOffset G )
                  ( ( NTP4VCOffset G ) +
                    ( NTP4VCSigned32 B ) ) ) /\
              ( ( NTP4VCOffset D ) = ( NTP4VCOffset H ) \/
                NTP4VCMapEqSub H F
                  ( NTP4VCOffset H )
                  ( ( NTP4VCOffset H ) +
                    ( NTP4VCSigned32 A ) ) ) ) ) ) ) )
$.

ntp4vc-close-pre-def $a
  |- ( NTP4VCClosePre A B C D E F G H I <->
      ( ( NTP4VCOk I ) = 1 /\
        ( ( 0 <_ ( NTP4VCSigned32 A ) /\
            ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B ) ) /\
          ( ( ( NTP4VCZr I ) = ( NTP4VCZone C ) /\
              ( ( NTP4VCZx I ) = ( NTP4VCZone D ) /\
                ( NTP4VCZy I ) = ( NTP4VCZone E ) ) ) /\
            ( ( ( NTP4VCLr I ) = B /\
                ( ( NTP4VCLx I ) = B /\
                  ( NTP4VCLy I ) = A ) ) /\
              ( NTP4VCOrderedTriple F G H
                  ( NTP4VCSigned32 B ) /\
                ( ( NTP4VCWritable C ) = 1 /\
                  ( NTP4VCWritable F ) = 1 ) ) ) ) ) ) ) )
$.

ntp4vc-final-post-def $a
  |- ( NTP4VCFinalPost A B C D E F G H I <->
      ( ( ( NTP4VCValue F ( NTP4VCSigned32 B ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 B ) ) ) x. I ) ) =
        ( ( NTP4VCValue D ( NTP4VCSigned32 B ) ) -
          ( NTP4VCValue E ( NTP4VCSigned32 A ) ) ) /\
        ( ( 0 <_ I /\ I <_ 1 ) /\
          ( NTP4VCFrame F C ( NTP4VCSigned32 B ) /\
            ( NTP4VCSamePelts G D /\
              ( NTP4VCSamePelts H E /\
                ( ( NTP4VCValue G ( NTP4VCSigned32 B ) ) =
                      ( NTP4VCValue D ( NTP4VCSigned32 B ) ) /\
                  ( ( NTP4VCValue H ( NTP4VCSigned32 A ) ) =
                        ( NTP4VCValue E ( NTP4VCSigned32 A ) ) /\
                    ( ( ( NTP4VCMin G ) = ( NTP4VCMin D ) /\
                        ( ( NTP4VCMax G ) = ( NTP4VCMax D ) /\
                          ( NTP4VCPlength G ) =
                          ( NTP4VCPlength D ) ) ) /\
                      ( ( ( NTP4VCMin H ) = ( NTP4VCMin E ) /\
                          ( ( NTP4VCMax H ) = ( NTP4VCMax E ) /\
                            ( NTP4VCPlength H ) =
                            ( NTP4VCPlength E ) ) ) /\
                        ( ( NTP4VCMin F ) = ( NTP4VCMin C ) /\
                          ( ( NTP4VCMax F ) = ( NTP4VCMax C ) /\
                            ( NTP4VCPlength F ) =
                            ( NTP4VCPlength C ) ) ) ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-close-transition-def $a
  |- ( NTP4VCCloseTransition A B C D E F G H I J K L M N O <->
      ( ( ( NTP4VCMax M ) =
            ( NTP4VCSigned32 ( NTP4VCMr I ) ) /\
          ( ( NTP4VCMax N ) =
              ( NTP4VCSigned32 ( NTP4VCMx I ) ) /\
            ( NTP4VCMax O ) =
              ( NTP4VCSigned32 ( NTP4VCMy I ) ) ) ) /\
        ( NTP4VCMapEqSubShift C M
            ( NTP4VCOffset J ) ( NTP4VCOffset M )
            ( NTP4VCSigned32 B ) /\
          ( NTP4VCMapEqSubShift D N
              ( NTP4VCOffset K ) ( NTP4VCOffset N )
              ( NTP4VCSigned32 B ) /\
            ( NTP4VCMapEqSubShift E O
                ( NTP4VCOffset L ) ( NTP4VCOffset O )
                ( NTP4VCSigned32 A ) /\
              ( NTP4VCFrame M F ( NTP4VCSigned32 B ) /\
                ( NTP4VCFrame N G ( NTP4VCSigned32 B ) /\
                  ( NTP4VCFrame O H ( NTP4VCSigned32 A ) /\
                    ( ( ( NTP4VCPlength M ) =
                          ( NTP4VCPlength F ) /\
                        ( ( NTP4VCPlength N ) =
                            ( NTP4VCPlength G ) /\
                          ( NTP4VCPlength O ) =
                            ( NTP4VCPlength H ) ) ) /\
                      ( ( NTP4VCMin M ) = ( NTP4VCMin F ) /\
                        ( ( NTP4VCMin N ) = ( NTP4VCMin G ) /\
                          ( NTP4VCMin O ) =
                            ( NTP4VCMin H ) ) ) ) ) ) ) ) ) ) ) )
$.

${
  $d p q r s t u v A B C D E F G H I J K L M N $.
  ntp4vc-close-obligation-def $a
    |- ( NTP4VCCloseObligation A B C D E F G H I J K L M N <->
        A. p e. ( NTP4VCAliasMem N )
          A. q e. ( NTP4VCPtr N )
            A. r e. ( NTP4VCPtr N )
              A. s e. ( NTP4VCPtr N )
                A. t e. ( NTP4VCPtr N )
                  A. u e. ( NTP4VCPtr N )
                    A. v e. ( NTP4VCPtr N )
                      ( NTP4VCSameAliasFields p L ->
                        ( NTP4VCViewEq q K ->
                          ( NTP4VCViewEq r J ->
                            ( NTP4VCViewEq s I ->
                              ( NTP4VCViewMinEq t H ->
                                ( NTP4VCViewMinEq u G ->
                                  ( NTP4VCViewMinEq v F ->
                                    ( NTP4VCCloseTransition
                                        A B I J K F G H p s r q v u t ->
                                      NTP4VCFinalPost
                                        A B C D E v u t M ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d p q r s A B C D E F G H I J K L M $.
  ntp4vc-after-wmpn-sub-def $a
    |- ( NTP4VCAfterWmpnSub A B C D E F G H I J K L M <->
        A. p e. ( NTP4VCPtr M )
          A. q e. ( NTP4VCPtr M )
            A. r e. ( NTP4VCPtr M )
              ( NTP4VCSnapshot p r K ->
                ( NTP4VCSnapshot q r J ->
                  ( NTP4VCNrSnapshot r I ->
                    A. s e. NTP4VCWord64
                      ( NTP4VCWmpnPost A B I r J K q p s ->
                        ( NTP4VCClosePre A B F G H r q p L /\
                          NTP4VCCloseObligation
                            A B C D E F G H r q p L s M ) ) ) ) ) )
  $.
$}

ntp4vc-opened-core-def $a
  |- ( NTP4VCOpenedCore A B C D E <->
      ( ( 0 <_ ( NTP4VCSigned32 A ) /\
          ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B ) ) /\
        ( ( NTP4VCValid C ( NTP4VCSigned32 B ) /\
            ( NTP4VCValid D ( NTP4VCSigned32 B ) /\
              NTP4VCValid E ( NTP4VCSigned32 A ) ) ) /\
          ( NTP4VCNonoverlap C D
              ( NTP4VCSigned32 B ) ( NTP4VCSigned32 B ) /\
            ( NTP4VCNonoverlap C E
                ( NTP4VCSigned32 B ) ( NTP4VCSigned32 A ) /\
              ( ( ( NTP4VCData C ) = ( NTP4VCData D ) /\
                  ( NTP4VCData D ) = ( NTP4VCData E ) ) /\
                ( NTP4VCWritable C ) = 1 ) ) ) ) ) )
$.

ntp4vc-open-sep-antecedent-def $a
  |- ( NTP4VCOpenSepAntecedent A B C D E F G H I J K L <->
      ( ( NTP4VCWritable I ) = 1 /\
        ( ( ( NTP4VCValue J ( NTP4VCSigned32 B ) ) =
              ( NTP4VCValue D ( NTP4VCSigned32 B ) ) /\
            ( NTP4VCValue K ( NTP4VCSigned32 A ) ) =
              ( NTP4VCValue E ( NTP4VCSigned32 A ) ) ) /\
          ( ( NTP4VCValid I ( NTP4VCSigned32 B ) /\
              ( NTP4VCValid J ( NTP4VCSigned32 B ) /\
                NTP4VCValid K ( NTP4VCSigned32 A ) ) ) /\
            ( NTP4VCOrderedTriple I J K
                ( NTP4VCSigned32 B ) /\
              ( ( ( NTP4VCZr L ) = ( NTP4VCZone F ) /\
                  ( ( NTP4VCZx L ) = ( NTP4VCZone G ) /\
                    ( NTP4VCZy L ) = ( NTP4VCZone H ) ) ) /\
                ( ( ( NTP4VCSigned32 ( NTP4VCMr L ) ) =
                      ( NTP4VCMax C ) /\
                    ( ( NTP4VCSigned32 ( NTP4VCMx L ) ) =
                        ( NTP4VCMax D ) /\
                      ( NTP4VCSigned32 ( NTP4VCMy L ) ) =
                        ( NTP4VCMax E ) ) ) /\
                  ( ( ( NTP4VCLr L ) = B /\
                      ( ( NTP4VCLx L ) = B /\
                        ( NTP4VCLy L ) = A ) ) /\
                    ( ( NTP4VCOk L ) = 1 /\
                      ( NTP4VCMapEqSubShift I F
                          ( NTP4VCOffset I )
                          ( NTP4VCOffset F )
                          ( NTP4VCSigned32 B ) /\
                        ( NTP4VCMapEqSubShift J G
                            ( NTP4VCOffset J )
                            ( NTP4VCOffset G )
                            ( NTP4VCSigned32 B ) /\
                          ( NTP4VCMapEqSubShift K H
                              ( NTP4VCOffset K )
                              ( NTP4VCOffset H )
                              ( NTP4VCSigned32 A ) /\
                            ( ( NTP4VCSamePelts F C /\
                                ( NTP4VCSamePelts G D /\
                                  NTP4VCSamePelts H E ) ) /\
                              ( ( ( NTP4VCPlength F ) =
                                    ( NTP4VCPlength C ) /\
                                  ( ( NTP4VCPlength G ) =
                                      ( NTP4VCPlength D ) /\
                                    ( NTP4VCPlength H ) =
                                      ( NTP4VCPlength E ) ) ) /\
                                ( ( ( NTP4VCMin F ) =
                                      ( NTP4VCMin C ) /\
                                    ( ( NTP4VCMin G ) =
                                        ( NTP4VCMin D ) /\
                                      ( NTP4VCMin H ) =
                                        ( NTP4VCMin E ) ) ) /\
                                  ( ( NTP4VCData I ) =
                                      ( NTP4VCData J ) /\
                                    ( NTP4VCData J ) =
                                      ( NTP4VCData K ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-opened-state-def $a
  |- ( NTP4VCOpenedState A B C D E F G H I J K L M <->
      ( NTP4VCOpenedCore A B I J K /\
        NTP4VCAfterWmpnSub
          A B C D E F G H I J K L M ) )
$.

${
  $d p q r s A B C D E F G H I $.
  ntp4vc-all-opened-states-def $a
    |- ( NTP4VCAllOpenedStates A B C D E F G H I <->
        A. p e. ( NTP4VCPtr I )
          A. q e. ( NTP4VCPtr I )
            A. r e. ( NTP4VCPtr I )
              A. s e. ( NTP4VCAliasMem I )
                ( NTP4VCOpenSepAntecedent
                    A B C D E F G H p q r s ->
                  NTP4VCOpenedState
                    A B C D E F G H p q r s I ) )
  $.
$}

${
  $d p q r A B C D E F $.
  ntp4vc-all-views-def $a
    |- ( NTP4VCAllViews A B C D E F <->
        A. p e. ( NTP4VCPtr F )
          A. q e. ( NTP4VCPtr F )
            A. r e. ( NTP4VCPtr F )
              ( NTP4VCViewEq p E ->
                ( NTP4VCViewEq q D ->
                  ( NTP4VCViewEq r C ->
                    NTP4VCAllOpenedStates
                      A B C D E r q p F ) ) ) )
  $.
$}

ntp4vc-sub-conclusion-def $a
  |- ( NTP4VCSubConclusion A B C D E F <->
      ( NTP4VCValid C ( NTP4VCSigned32 B ) /\
        ( NTP4VCValid D ( NTP4VCSigned32 B ) /\
          ( NTP4VCValid E ( NTP4VCSigned32 A ) /\
            ( ( NTP4VCWritable C ) = 1 /\
              ( 0 <_ ( NTP4VCSigned32 A ) /\
                ( ( NTP4VCSigned32 A ) <_
                    ( NTP4VCSigned32 B ) /\
                  NTP4VCAllViews A B C D E F ) ) ) ) ) ) )
$.

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
  ntp4vc-r-writable $e
    |- ( NTP4VCWritable C ) = 1
  $.

  ntp4vc-sub-statement $a
    |- NTP4VCSubConclusion A B C D E Z
  $.
$}
