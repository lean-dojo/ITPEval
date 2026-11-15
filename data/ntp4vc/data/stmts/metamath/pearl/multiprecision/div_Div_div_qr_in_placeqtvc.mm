$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div_qr_in_placeqtvc: the verification
  condition for in-place multiprecision quotient-and-remainder division,
  including one-limb, two-limb, normalized, and shifted multi-limb branches,
  pointer framing and updates, quotient adjustment, and the final Euclidean
  quotient-remainder relation. This file contains no proof.

  Source 32- and 64-bit words are represented exactly by their unsigned
  integer intervals, with the source signed interpretation on 32-bit words.
  A pointer retains a total integer-indexed limb map, independent length,
  offset and bounds, writability, and an arbitrary nonempty zone. The
  predicates below are definitional abbreviations for the source formulas.
  Deterministic lets, proposition-valued conditionals, Boolean witnesses
  characterized in both directions, and uniquely representable word casts
  are expanded to their bidirectionally equivalent arithmetic branches.
  All procedure-result pointers and limbs remain universally quantified.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCSameMeta NTP4VCUpdateLaw NTP4VCWrite
  NTP4VCBounds NTP4VCMapEqSubShift NTP4VCOutsideFrame NTP4VCCopyFrame
  NTP4VCNormalized NTP4VCFinal NTP4VCDivRel NTP4VCCopyFinal
  NTP4VCShiftCopyFinal
  NTP4VCQuotientFinish NTP4VCCopyAndFinish NTP4VCShiftAndFinish
  NTP4VCDiv2Direct NTP4VCDiv2Shifted NTP4VCDivNDirect
  NTP4VCDivNShifted NTP4VCClzCondition NTP4VCDirect2
  NTP4VCShifted2 NTP4VCDirectN NTP4VCShiftedN NTP4VCSy1
  NTP4VCSy2 NTP4VCGeneral NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syn $a wff NTP4VCInt32InBounds A $.
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
ntp4vc-same-meta-syn $a wff NTP4VCSameMeta A B $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-write-syn $a wff NTP4VCWrite A B C D $.
ntp4vc-bounds-syn $a wff NTP4VCBounds A B $.
ntp4vc-map-eq-syn $a wff NTP4VCMapEqSubShift A B C $.
ntp4vc-outside-syn $a wff NTP4VCOutsideFrame A B C $.
ntp4vc-copy-frame-syn $a wff NTP4VCCopyFrame A B C D $.
ntp4vc-normalized-syn $a wff NTP4VCNormalized A B $.
ntp4vc-final-syn $a wff NTP4VCFinal A B C D E F $.
ntp4vc-div-rel-syn $a wff NTP4VCDivRel A B C D E F G $.
ntp4vc-copy-final-syn $a wff NTP4VCCopyFinal A B C D E F $.
ntp4vc-shift-copy-final-syn
  $a wff NTP4VCShiftCopyFinal A B C D E F G H $.
ntp4vc-quotient-finish-syn
  $a wff NTP4VCQuotientFinish A B C D E F G $.
ntp4vc-copy-and-finish-syn
  $a wff NTP4VCCopyAndFinish A B C D E F G $.
ntp4vc-shift-and-finish-syn
  $a wff NTP4VCShiftAndFinish A B C D E F G H I $.
ntp4vc-div2-direct-syn $a wff NTP4VCDiv2Direct A B C D E F $.
ntp4vc-div2-shifted-syn
  $a wff NTP4VCDiv2Shifted A B C D E F G H $.
ntp4vc-divn-direct-syn
  $a wff NTP4VCDivNDirect A B C D E F G $.
ntp4vc-divn-shifted-syn
  $a wff NTP4VCDivNShifted A B C D E F G H I $.
ntp4vc-clz-condition-syn $a wff NTP4VCClzCondition A B $.
ntp4vc-direct2-syn $a wff NTP4VCDirect2 A B C D E F $.
ntp4vc-shifted2-syn $a wff NTP4VCShifted2 A B C D E F G H $.
ntp4vc-directn-syn $a wff NTP4VCDirectN A B C D E F G $.
ntp4vc-shiftedn-syn $a wff NTP4VCShiftedN A B C D E F G H I $.
ntp4vc-sy1-syn $a wff NTP4VCSy1 A B C D E $.
ntp4vc-sy2-syn $a wff NTP4VCSy2 A B C D E F G $.
ntp4vc-general-syn $a wff NTP4VCGeneral A B C D E F G $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C D E F G H $.

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

ntp4vc-int32-bounds-def $a
  |- ( NTP4VCInt32InBounds A <->
      ( A e. ZZ /\
        ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) ) ) )
$.

ntp4vc-ptr-def $a
  |- ( NTP4VCPtr A ) =
      ( ( ( NTP4VCWord64 ^m ZZ ) X. NN0 ) X.
        ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) ) )
$.

ntp4vc-data-def $a |- ( NTP4VCData A ) = ( 1st ` A ) $.
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
  |- ( NTP4VCPelts A B ) = ( ( 1st ` ( NTP4VCData A ) ) ` B )
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
  $d k A $.  $d k B $.
  ntp4vc-value-def $a
    |- ( NTP4VCValue A B ) =
        sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
          ( ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) ) x.
            ( ( 2 ^ ; 6 4 ) ^ k ) )
  $.
$}

ntp4vc-same-meta-def $a
  |- ( NTP4VCSameMeta A B <->
      ( ( NTP4VCLength A ) = ( NTP4VCLength B ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

${
  $d j A $.  $d j B $.  $d j C $.  $d j D $.
  ntp4vc-update-law-def $a
    |- ( NTP4VCUpdateLaw A B C D <->
        A. j e. ZZ
          ( ( NTP4VCPelts B j ) =
            if ( j = C , D , ( NTP4VCPelts A j ) ) ) )
  $.
$}

ntp4vc-write-def $a
  |- ( NTP4VCWrite A B C D <->
      ( NTP4VCSameMeta A B /\
        ( NTP4VCUpdateLaw B A C D /\
          ( NTP4VCPelts A C ) = D ) ) )
$.

ntp4vc-bounds-def $a
  |- ( NTP4VCBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A ) ) )
$.

${
  $d j A $.  $d j B $.  $d j C $.
  ntp4vc-map-eq-def $a
    |- ( NTP4VCMapEqSubShift A B C <->
        A. j e. ZZ
          ( ( ( NTP4VCOffset A ) <_ j /\
              j < ( ( NTP4VCOffset A ) + C ) ) ->
            ( NTP4VCPelts A j ) =
            ( NTP4VCPelts B
              ( ( NTP4VCOffset B ) +
                ( j - ( NTP4VCOffset A ) ) ) ) ) )
  $.
$}

${
  $d j A $.  $d j B $.  $d j C $.
  ntp4vc-outside-def $a
    |- ( NTP4VCOutsideFrame A B C <->
        A. j e. ZZ
          ( ( j < ( NTP4VCOffset A ) \/
              ( ( NTP4VCOffset A ) + C ) <_ j ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

ntp4vc-copy-frame-def $a
  |- ( NTP4VCCopyFrame A B C D <->
      ( NTP4VCSameMeta A C /\
        ( NTP4VCMapEqSubShift A B D /\
          NTP4VCOutsideFrame A C D ) ) )
$.

ntp4vc-normalized-def $a
  |- ( NTP4VCNormalized A B <->
      ( NTP4VCValid A ( NTP4VCSigned32 B ) /\
        ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_
          ( NTP4VCPelts A
            ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) ) - 1 ) ) ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C D E F <->
      ( ( NTP4VCValue A ( NTP4VCSigned32 E ) ) =
        ( ( NTP4VCValue B
              ( ( ( NTP4VCSigned32 E ) -
                  ( NTP4VCSigned32 F ) ) + 1 ) ) x.
            ( NTP4VCValue C ( NTP4VCSigned32 F ) ) ) +
          ( NTP4VCValue D ( NTP4VCSigned32 F ) ) ) /\
        ( NTP4VCValue D ( NTP4VCSigned32 F ) ) <
        ( NTP4VCValue C ( NTP4VCSigned32 F ) ) )
$.

ntp4vc-div-rel-def $a
  |- ( NTP4VCDivRel A B C D E F G <->
      ( ( NTP4VCValue A E ) =
        ( ( ( NTP4VCValue B ( E - F ) ) +
            ( ( ( 2 ^ ; 6 4 ) ^ ( E - F ) ) x. G ) ) x.
          ( NTP4VCValue C F ) +
          ( NTP4VCValue D F ) ) /\
        ( ( NTP4VCValue D F ) < ( NTP4VCValue C F ) /\
          ( 0 <_ G /\ G <_ 1 ) ) ) )
$.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.
  ntp4vc-copy-final-def $a
    |- ( NTP4VCCopyFinal A B C D E F <->
        ( ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
            ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
              ( NTP4VCWritable A ) = 1 ) ) /\
          A. x e. ( NTP4VCPtr _V )
            ( NTP4VCCopyFrame x D A ( NTP4VCSigned32 F ) ->
              NTP4VCFinal A C B x E F ) ) )
  $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.
  $d l A $.  $d l B $.  $d l C $.  $d l D $.
  $d l E $.  $d l F $.  $d l G $.  $d l H $.
  $d x l $.
  ntp4vc-shift-copy-final-def $a
    |- ( NTP4VCShiftCopyFinal A B C D E F G H <->
        ( ( 0 <_ G /\
            ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
              ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
                ( ( 0 < G /\ G < 6 4 ) /\
                  ( 0 < ( NTP4VCSigned32 F ) /\
                    ( NTP4VCWritable A ) = 1 ) ) ) ) ) /\
          A. x e. ( NTP4VCPtr _V )
            ( NTP4VCSameMeta x A ->
              A. l e. NTP4VCWord64
                ( ( l +
                    ( ( 2 ^ ; 6 4 ) x.
                      ( NTP4VCValue x ( NTP4VCSigned32 F ) ) ) ) =
                  ( ( NTP4VCValue D ( NTP4VCSigned32 F ) ) x.
                    ( 2 ^ ( 6 4 - G ) ) ) ->
                  ( ( NTP4VCValue D ( NTP4VCSigned32 F ) ) =
                    ( H x.
                      ( NTP4VCValue x ( NTP4VCSigned32 F ) ) ) /\
                    NTP4VCFinal A C B x E F ) ) ) ) )
  $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d q E $.  $d q F $.  $d q G $.
  ntp4vc-quotient-finish-def $a
    |- ( NTP4VCQuotientFinish A B C D E F G <->
        ( ( ( G = 0 /\
              ( NTP4VCBounds C
                  ( ( NTP4VCSigned32 E ) -
                    ( NTP4VCSigned32 F ) ) /\
                ( ( NTP4VCWritable C ) = 1 /\
                  ( NTP4VCInt32InBounds
                      ( ( NTP4VCSigned32 E ) -
                        ( NTP4VCSigned32 F ) ) /\
                    A. q e. ( NTP4VCPtr _V )
                      ( NTP4VCWrite q C
                          ( ( NTP4VCOffset q ) +
                            ( ( NTP4VCSigned32 E ) -
                              ( NTP4VCSigned32 F ) ) ) 0 ->
                        ( NTP4VCValue q
                            ( ( ( NTP4VCSigned32 E ) -
                                ( NTP4VCSigned32 F ) ) + 1 ) ) =
                        ( NTP4VCValue C
                            ( ( ( NTP4VCSigned32 E ) -
                                ( NTP4VCSigned32 F ) ) + G ) ) ) ) ) ) ) \/
            ( G = 1 /\
              ( NTP4VCValue C
                  ( ( ( NTP4VCSigned32 E ) -
                      ( NTP4VCSigned32 F ) ) + 1 ) ) =
              ( NTP4VCValue C
                  ( ( ( NTP4VCSigned32 E ) -
                      ( NTP4VCSigned32 F ) ) + G ) ) ) ) /\
          A. q e. ( NTP4VCPtr _V )
            ( ( NTP4VCSameMeta q C /\
                ( NTP4VCValue q
                    ( ( ( NTP4VCSigned32 E ) -
                        ( NTP4VCSigned32 F ) ) + 1 ) ) =
                ( NTP4VCValue C
                    ( ( ( NTP4VCSigned32 E ) -
                        ( NTP4VCSigned32 F ) ) + G ) ) ) ->
              NTP4VCFinal A q B D E F ) ) )
  $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.
  ntp4vc-copy-and-finish-def $a
    |- ( NTP4VCCopyAndFinish A B C D E F G <->
        ( ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
            ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
              ( NTP4VCWritable A ) = 1 ) ) /\
          A. x e. ( NTP4VCPtr _V )
            ( NTP4VCCopyFrame x D A ( NTP4VCSigned32 F ) ->
              NTP4VCQuotientFinish A B C x E F G ) ) )
  $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.  $d x I $.
  $d l A $.  $d l B $.  $d l C $.  $d l D $.
  $d l E $.  $d l F $.  $d l G $.  $d l H $.  $d l I $.
  $d x l $.
  ntp4vc-shift-and-finish-def $a
    |- ( NTP4VCShiftAndFinish A B C D E F G H I <->
        ( ( 0 <_ H /\
            ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
              ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
                ( ( 0 < H /\ H < 6 4 ) /\
                  ( 0 < ( NTP4VCSigned32 F ) /\
                    ( NTP4VCWritable A ) = 1 ) ) ) ) ) /\
          A. x e. ( NTP4VCPtr _V )
            ( NTP4VCSameMeta x A ->
              A. l e. NTP4VCWord64
                ( ( l +
                    ( ( 2 ^ ; 6 4 ) x.
                      ( NTP4VCValue x ( NTP4VCSigned32 F ) ) ) ) =
                  ( ( NTP4VCValue D ( NTP4VCSigned32 F ) ) x.
                    ( 2 ^ ( 6 4 - H ) ) ) ->
                  ( ( NTP4VCValue D ( NTP4VCSigned32 F ) ) =
                    ( I x.
                      ( NTP4VCValue x ( NTP4VCSigned32 F ) ) ) /\
                    NTP4VCQuotientFinish A B C x E F G ) ) ) ) )
  $.
$}

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.  $d n E $.  $d n F $.
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.  $d q F $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.  $d h E $.  $d h F $.
  $d n q $.  $d n h $.  $d q h $.
  ntp4vc-div2-direct-def $a
    |- ( NTP4VCDiv2Direct A B C D E F <->
        ( ( 2 <_ ( ( NTP4VCSigned32 E ) + 1 ) /\
            ( NTP4VCValid D ( ( NTP4VCSigned32 E ) + 1 ) /\
              ( NTP4VCValid B 2 /\
                ( NTP4VCValid C
                    ( ( ( NTP4VCSigned32 E ) + 1 ) - 2 ) /\
                  ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_
                    ( NTP4VCPelts B
                      ( ( NTP4VCOffset B ) + 1 ) ) /\
                    ( ( NTP4VCWritable C ) = 1 /\
                      ( NTP4VCWritable D ) = 1 ) ) ) ) ) ) /\
          A. n e. ( NTP4VCPtr _V )
            A. q e. ( NTP4VCPtr _V )
              ( ( NTP4VCSameMeta n D /\ NTP4VCSameMeta q C ) ->
                A. h e. NTP4VCWord64
                  ( NTP4VCDivRel D q B n
                      ( ( NTP4VCSigned32 E ) + 1 ) 2 h ->
                    NTP4VCCopyFinal A B q n E F ) ) ) )
  $.
$}

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.  $d n H $.
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d q E $.  $d q F $.  $d q G $.  $d q H $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.
  $d h E $.  $d h F $.  $d h G $.  $d h H $.
  $d n q $.  $d n h $.  $d q h $.
  ntp4vc-div2-shifted-def $a
    |- ( NTP4VCDiv2Shifted A B C D E F G H <->
        ( ( 2 <_ ( ( NTP4VCSigned32 F ) + 1 ) /\
            ( NTP4VCValid D ( ( NTP4VCSigned32 F ) + 1 ) /\
              ( NTP4VCValid E 2 /\
                ( NTP4VCValid C
                    ( ( ( NTP4VCSigned32 F ) + 1 ) - 2 ) /\
                  ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_
                    ( NTP4VCPelts E
                      ( ( NTP4VCOffset E ) + 1 ) ) /\
                    ( ( NTP4VCWritable C ) = 1 /\
                      ( NTP4VCWritable D ) = 1 ) ) ) ) ) ) /\
          A. n e. ( NTP4VCPtr _V )
            A. q e. ( NTP4VCPtr _V )
              ( ( NTP4VCSameMeta n D /\ NTP4VCSameMeta q C ) ->
                A. h e. NTP4VCWord64
                  ( NTP4VCDivRel D q E n
                      ( ( NTP4VCSigned32 F ) + 1 ) 2 h ->
                    NTP4VCShiftCopyFinal A B q n F G
                      ( NTP4VCSigned32 H )
                      ( 2 ^ ( NTP4VCSigned32 H ) ) ) ) ) )
  $.
$}

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d q E $.  $d q F $.  $d q G $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.
  $d h E $.  $d h F $.  $d h G $.
  $d n q $.  $d n h $.  $d q h $.
  ntp4vc-divn-direct-def $a
    |- ( NTP4VCDivNDirect A B C D E F G <->
        ( ( ( 3 <_ ( NTP4VCSigned32 F ) /\
              ( NTP4VCSigned32 F ) <_
              ( ( NTP4VCSigned32 E ) + G ) ) /\
            ( NTP4VCValid D
                ( ( NTP4VCSigned32 E ) + G ) /\
              ( NTP4VCValid B ( NTP4VCSigned32 F ) /\
                ( NTP4VCValid C
                    ( ( ( NTP4VCSigned32 E ) + G ) -
                      ( NTP4VCSigned32 F ) ) /\
                  ( ( NTP4VCWritable C ) = 1 /\
                    ( ( NTP4VCWritable D ) = 1 /\
                      NTP4VCNormalized B F ) ) ) ) ) ) /\
          A. n e. ( NTP4VCPtr _V )
            A. q e. ( NTP4VCPtr _V )
              ( ( NTP4VCSameMeta n D /\ NTP4VCSameMeta q C ) ->
                A. h e. NTP4VCWord64
                  ( NTP4VCDivRel D q B n
                      ( ( NTP4VCSigned32 E ) + G )
                      ( NTP4VCSigned32 F ) h ->
                    NTP4VCCopyAndFinish A B q n E F G ) ) ) )
  $.
$}

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.  $d n H $.  $d n I $.
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d q E $.  $d q F $.  $d q G $.  $d q H $.  $d q I $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.
  $d h E $.  $d h F $.  $d h G $.  $d h H $.  $d h I $.
  $d n q $.  $d n h $.  $d q h $.
  ntp4vc-divn-shifted-def $a
    |- ( NTP4VCDivNShifted A B C D E F G H I <->
        ( ( ( 3 <_ ( NTP4VCSigned32 G ) /\
              ( NTP4VCSigned32 G ) <_
              ( ( NTP4VCSigned32 F ) + H ) ) /\
            ( NTP4VCValid D
                ( ( NTP4VCSigned32 F ) + H ) /\
              ( NTP4VCValid E ( NTP4VCSigned32 G ) /\
                ( NTP4VCValid C
                    ( ( ( NTP4VCSigned32 F ) + H ) -
                      ( NTP4VCSigned32 G ) ) /\
                  ( ( NTP4VCWritable C ) = 1 /\
                    ( ( NTP4VCWritable D ) = 1 /\
                      NTP4VCNormalized E G ) ) ) ) ) ) /\
          A. n e. ( NTP4VCPtr _V )
            A. q e. ( NTP4VCPtr _V )
              ( ( NTP4VCSameMeta n D /\ NTP4VCSameMeta q C ) ->
                A. h e. NTP4VCWord64
                  ( NTP4VCDivRel D q E n
                      ( ( NTP4VCSigned32 F ) + H )
                      ( NTP4VCSigned32 G ) h ->
                    NTP4VCShiftAndFinish A B q n F G H
                      ( NTP4VCSigned32 I )
                      ( 2 ^ ( NTP4VCSigned32 I ) ) ) ) ) )
  $.
$}

ntp4vc-clz-condition-def $a
  |- ( NTP4VCClzCondition A B <->
      ( ( ( 2 ^ ( NTP4VCSigned32 A ) ) x. B ) <
          ( 2 ^ ; 6 4 ) /\
        ( ( 2 ^ ; 6 4 ) <_
            ( ( 2 x. ( 2 ^ ( NTP4VCSigned32 A ) ) ) x. B ) /\
          ( ( 0 <_ ( NTP4VCSigned32 A ) /\
              ( NTP4VCSigned32 A ) < 6 4 ) /\
            ( ( ( 2 ^ ( NTP4VCSigned32 A ) ) x. B ) <_
              ( ( 2 ^ ; 6 4 ) -
                ( 2 ^ ( NTP4VCSigned32 A ) ) ) ) ) ) ) )
$.

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.  $d n E $.  $d n F $.
  $d m A $.  $d m B $.  $d m C $.  $d m D $.  $d m E $.  $d m F $.
  $d n m $.
  ntp4vc-direct2-def $a
    |- ( NTP4VCDirect2 A B C D E F <->
        ( ( NTP4VCValid A ( NTP4VCSigned32 E ) /\
            ( NTP4VCValid D ( NTP4VCSigned32 E ) /\
              ( NTP4VCWritable D ) = 1 ) ) /\
          A. n e. ( NTP4VCPtr _V )
            ( NTP4VCCopyFrame n A D ( NTP4VCSigned32 E ) ->
              ( ( NTP4VCBounds n ( NTP4VCSigned32 E ) /\
                  ( NTP4VCWritable n ) = 1 ) /\
                A. m e. ( NTP4VCPtr _V )
                  ( NTP4VCWrite m n
                      ( ( NTP4VCOffset m ) +
                        ( NTP4VCSigned32 E ) ) 0 ->
                    ( NTP4VCInt32InBounds
                        ( ( NTP4VCSigned32 E ) + 1 ) /\
                      NTP4VCDiv2Direct A B C m E F ) ) ) ) ) )
  $.
$}

${
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.  $d y H $.
  $d c A $.  $d c B $.  $d c C $.  $d c D $.
  $d c E $.  $d c F $.  $d c G $.  $d c H $.
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.  $d n H $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.
  $d h E $.  $d h F $.  $d h G $.  $d h H $.
  $d m A $.  $d m B $.  $d m C $.  $d m D $.
  $d m E $.  $d m F $.  $d m G $.  $d m H $.
  $d y c $.  $d y n $.  $d y h $.  $d y m $.
  $d c n $.  $d c h $.  $d c m $.  $d n h $.  $d n m $.  $d h m $.
  ntp4vc-shifted2-def $a
    |- ( NTP4VCShifted2 A B C D E F G H <->
        ( ( ( 0 < ( NTP4VCSigned32 H ) /\
              ( NTP4VCSigned32 H ) < 6 4 ) /\
            ( NTP4VCValid E ( NTP4VCSigned32 G ) /\
              ( NTP4VCValid B ( NTP4VCSigned32 G ) /\
                ( ( NTP4VCWritable E ) = 1 /\
                  0 < ( NTP4VCSigned32 G ) ) ) ) ) /\
          A. y e. ( NTP4VCPtr _V )
            ( NTP4VCSameMeta y E ->
              A. c e. NTP4VCWord64
                ( ( ( NTP4VCValue y ( NTP4VCSigned32 G ) ) +
                    ( ( ( 2 ^ ; 6 4 ) ^
                        ( NTP4VCSigned32 G ) ) x. c ) ) =
                  ( ( NTP4VCValue B ( NTP4VCSigned32 G ) ) x.
                    ( 2 ^ ( NTP4VCSigned32 H ) ) ) ->
                  ( ( NTP4VCNormalized y G /\
                      ( NTP4VCValue y ( NTP4VCSigned32 G ) ) =
                      ( ( 2 ^ ( NTP4VCSigned32 H ) ) x.
                        ( NTP4VCValue B
                          ( NTP4VCSigned32 G ) ) ) ) /\
                    ( ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
                        ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
                          ( ( NTP4VCWritable D ) = 1 /\
                            0 < ( NTP4VCSigned32 F ) ) ) ) /\
                      A. n e. ( NTP4VCPtr _V )
                        ( NTP4VCSameMeta n D ->
                          A. h e. NTP4VCWord64
                            ( ( ( NTP4VCValue n
                                    ( NTP4VCSigned32 F ) ) +
                                  ( ( ( 2 ^ ; 6 4 ) ^
                                      ( NTP4VCSigned32 F ) ) x. h ) ) =
                                ( ( NTP4VCValue A
                                      ( NTP4VCSigned32 F ) ) x.
                                  ( 2 ^ ( NTP4VCSigned32 H ) ) ) ->
                              ( ( NTP4VCBounds n
                                    ( NTP4VCSigned32 F ) /\
                                  ( NTP4VCWritable n ) = 1 ) /\
                                A. m e.
                                  ( NTP4VCPtr _V )
                                  ( NTP4VCWrite m n
                                      ( ( NTP4VCOffset m ) +
                                        ( NTP4VCSigned32 F ) ) h ->
                                    ( ( NTP4VCValue m
                                          ( ( NTP4VCSigned32 F ) + 1 ) ) =
                                        ( ( 2 ^
                                            ( NTP4VCSigned32 H ) ) x.
                                          ( NTP4VCValue A
                                            ( NTP4VCSigned32 F ) ) ) /\
                                      ( NTP4VCInt32InBounds
                                          ( ( NTP4VCSigned32 F ) + 1 ) /\
                                        NTP4VCDiv2Shifted
                                          A B C m y F G H ) ) ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.
  $d m A $.  $d m B $.  $d m C $.  $d m D $.
  $d m E $.  $d m F $.  $d m G $.
  $d n m $.
  ntp4vc-directn-def $a
    |- ( NTP4VCDirectN A B C D E F G <->
        ( ( NTP4VCValid A ( NTP4VCSigned32 E ) /\
            ( NTP4VCValid D ( NTP4VCSigned32 E ) /\
              ( NTP4VCWritable D ) = 1 ) ) /\
          A. n e. ( NTP4VCPtr _V )
            ( NTP4VCCopyFrame n A D ( NTP4VCSigned32 E ) ->
              ( ( NTP4VCBounds n ( NTP4VCSigned32 E ) /\
                  ( NTP4VCWritable n ) = 1 ) /\
                A. m e. ( NTP4VCPtr _V )
                  ( NTP4VCWrite m n
                      ( ( NTP4VCOffset m ) +
                        ( NTP4VCSigned32 E ) ) 0 ->
                    ( NTP4VCInt32InBounds
                        ( ( NTP4VCSigned32 E ) + G ) /\
                      NTP4VCDivNDirect A B C m E F G ) ) ) ) ) )
  $.
$}

${
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.  $d y H $.  $d y I $.
  $d c A $.  $d c B $.  $d c C $.  $d c D $.
  $d c E $.  $d c F $.  $d c G $.  $d c H $.  $d c I $.
  $d n A $.  $d n B $.  $d n C $.  $d n D $.
  $d n E $.  $d n F $.  $d n G $.  $d n H $.  $d n I $.
  $d h A $.  $d h B $.  $d h C $.  $d h D $.
  $d h E $.  $d h F $.  $d h G $.  $d h H $.  $d h I $.
  $d m A $.  $d m B $.  $d m C $.  $d m D $.
  $d m E $.  $d m F $.  $d m G $.  $d m H $.  $d m I $.
  $d y c $.  $d y n $.  $d y h $.  $d y m $.
  $d c n $.  $d c h $.  $d c m $.  $d n h $.  $d n m $.  $d h m $.
  ntp4vc-shiftedn-def $a
    |- ( NTP4VCShiftedN A B C D E F G H I <->
        ( ( ( 0 < ( NTP4VCSigned32 I ) /\
              ( NTP4VCSigned32 I ) < 6 4 ) /\
            ( NTP4VCValid E ( NTP4VCSigned32 G ) /\
              ( NTP4VCValid B ( NTP4VCSigned32 G ) /\
                ( ( NTP4VCWritable E ) = 1 /\
                  0 < ( NTP4VCSigned32 G ) ) ) ) ) /\
          A. y e. ( NTP4VCPtr _V )
            ( NTP4VCSameMeta y E ->
              A. c e. NTP4VCWord64
                ( ( ( NTP4VCValue y ( NTP4VCSigned32 G ) ) +
                    ( ( ( 2 ^ ; 6 4 ) ^
                        ( NTP4VCSigned32 G ) ) x. c ) ) =
                  ( ( NTP4VCValue B ( NTP4VCSigned32 G ) ) x.
                    ( 2 ^ ( NTP4VCSigned32 I ) ) ) ->
                  ( ( NTP4VCValid D ( NTP4VCSigned32 F ) /\
                      ( NTP4VCValid A ( NTP4VCSigned32 F ) /\
                        ( ( NTP4VCWritable D ) = 1 /\
                          0 < ( NTP4VCSigned32 F ) ) ) ) /\
                    A. n e. ( NTP4VCPtr _V )
                      ( NTP4VCSameMeta n D ->
                        A. h e. NTP4VCWord64
                          ( ( ( NTP4VCValue n
                                  ( NTP4VCSigned32 F ) ) +
                                ( ( ( 2 ^ ; 6 4 ) ^
                                    ( NTP4VCSigned32 F ) ) x. h ) ) =
                              ( ( NTP4VCValue A
                                    ( NTP4VCSigned32 F ) ) x.
                                ( 2 ^ ( NTP4VCSigned32 I ) ) ) ->
                            ( ( NTP4VCBounds n
                                  ( NTP4VCSigned32 F ) /\
                                ( NTP4VCWritable n ) = 1 ) /\
                              A. m e.
                                ( NTP4VCPtr _V )
                                ( NTP4VCWrite m n
                                    ( ( NTP4VCOffset m ) +
                                      ( NTP4VCSigned32 F ) ) h ->
                                  ( NTP4VCInt32InBounds
                                      ( ( NTP4VCSigned32 F ) + H ) /\
                                    NTP4VCDivNShifted
                                      A B C m y F G H I ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d l A $.  $d l B $.  $d l C $.  $d l D $.  $d l E $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d q l $.  $d q x $.  $d l x $.
  ntp4vc-sy1-def $a
    |- ( NTP4VCSy1 A B C D E <->
        ( NTP4VCBounds B 0 /\
          ( ( NTP4VCValid A ( NTP4VCSigned32 D ) /\
              ( NTP4VCValid C ( NTP4VCSigned32 D ) /\
                ( ( NTP4VCWritable C ) = 1 /\
                  ( 0 < ( NTP4VCSigned32 D ) /\
                    0 < ( NTP4VCPelts B
                      ( NTP4VCOffset B ) ) ) ) ) ) /\
            A. q e. ( NTP4VCPtr _V )
              ( NTP4VCSameMeta q C ->
                A. l e. NTP4VCWord64
                  ( ( ( NTP4VCValue A ( NTP4VCSigned32 D ) ) =
                      ( ( NTP4VCValue q
                            ( NTP4VCSigned32 D ) ) x.
                          ( NTP4VCPelts B
                            ( NTP4VCOffset B ) ) ) + l ) /\
                      l < ( NTP4VCPelts B
                        ( NTP4VCOffset B ) ) ) ->
                    ( ( NTP4VCBounds A 0 /\
                        ( NTP4VCWritable A ) = 1 ) /\
                      A. x e. ( NTP4VCPtr _V )
                        ( NTP4VCWrite x A
                            ( NTP4VCOffset x ) l ->
                          NTP4VCFinal A q B x D E ) ) ) ) ) )
  $.
$}

${
  $d c A $.  $d c B $.  $d c C $.  $d c D $.
  $d c E $.  $d c F $.  $d c G $.
  ntp4vc-sy2-def $a
    |- ( NTP4VCSy2 A B C D E F G <->
        ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 G ) - 1 ) /\
          ( NTP4VCBounds B ( ( NTP4VCSigned32 G ) - 1 ) /\
            ( 0 < ( NTP4VCPelts B
                ( ( ( NTP4VCOffset B ) +
                    ( NTP4VCSigned32 G ) ) - 1 ) ) /\
              A. c e. NTP4VCWord32
                ( NTP4VCClzCondition c
                    ( NTP4VCPelts B
                      ( ( ( NTP4VCOffset B ) +
                          ( NTP4VCSigned32 G ) ) - 1 ) ) ->
                  ( ( ( NTP4VCSigned32 c ) = 0 ->
                        NTP4VCDirect2 A B C D F G ) /\
                    ( ( NTP4VCSigned32 c ) =/= 0 ->
                        NTP4VCShifted2 A B C D E F G c ) ) ) ) ) ) )
  $.
$}

${
  $d c A $.  $d c B $.  $d c C $.  $d c D $.
  $d c E $.  $d c F $.  $d c G $.
  ntp4vc-general-def $a
    |- ( NTP4VCGeneral A B C D E F G <->
        ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 G ) - 1 ) /\
          ( NTP4VCBounds B ( ( NTP4VCSigned32 G ) - 1 ) /\
            ( NTP4VCInt32InBounds
                ( ( NTP4VCSigned32 F ) - 1 ) /\
              ( NTP4VCBounds A ( ( NTP4VCSigned32 F ) - 1 ) /\
                ( 0 < ( NTP4VCPelts B
                    ( ( ( NTP4VCOffset B ) +
                        ( NTP4VCSigned32 G ) ) - 1 ) ) /\
                  A. c e. NTP4VCWord32
                    ( NTP4VCClzCondition c
                        ( NTP4VCPelts B
                          ( ( ( NTP4VCOffset B ) +
                              ( NTP4VCSigned32 G ) ) - 1 ) ) ->
                      ( ( ( NTP4VCSigned32 c ) = 0 ->
                            NTP4VCDirectN A B C D F G
                              if (
                                ( NTP4VCPelts B
                                  ( ( ( NTP4VCOffset B ) +
                                      ( NTP4VCSigned32 G ) ) - 1 ) ) <_
                                ( NTP4VCPelts A
                                  ( ( ( NTP4VCOffset A ) +
                                      ( NTP4VCSigned32 F ) ) - 1 ) ) ,
                                1 , 0 ) ) /\
                        ( ( NTP4VCSigned32 c ) =/= 0 ->
                            NTP4VCShiftedN A B C D E F G
                              if (
                                ( NTP4VCPelts B
                                  ( ( ( NTP4VCOffset B ) +
                                      ( NTP4VCSigned32 G ) ) - 1 ) ) <_
                                ( NTP4VCPelts A
                                  ( ( ( NTP4VCOffset A ) +
                                      ( NTP4VCSigned32 F ) ) - 1 ) ) ,
                                1 , 0 ) c ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d b A $.  $d b B $.  $d b C $.  $d b D $.
  $d b E $.  $d b F $.  $d b G $.  $d b H $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D E F G H <->
        ( ( H = 1 -> NTP4VCSy1 C D E B A ) /\
          ( H =/= 1 ->
            A. b e. { 0 , 1 }
              ( ( ( ( NTP4VCSigned32 A ) = 2 -> b = 1 ) /\
                  ( b = 1 -> A = 2 ) ) ->
                ( ( b = 1 -> NTP4VCSy2 C D E F G B A ) /\
                  ( b =/= 1 -> NTP4VCGeneral C D E F G B A ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sy-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-x-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-q-type $e |- E e. ( NTP4VCPtr Z ) $.
  ntp4vc-nx-type $e |- F e. ( NTP4VCPtr Z ) $.
  ntp4vc-ny-type $e |- G e. ( NTP4VCPtr Z ) $.
  ntp4vc-o1-type $e |- H e. { 0 , 1 } $.
  ntp4vc-sy-positive $e |- 1 <_ ( NTP4VCSigned32 A ) $.
  ntp4vc-size-order $e
    |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B )
  $.
  ntp4vc-sx-upper $e
    |- ( NTP4VCSigned32 B ) <_ ( ( ( 2 ^ ; 3 1 ) - 1 ) - 1 )
  $.
  ntp4vc-x-valid $e |- NTP4VCValid C ( NTP4VCSigned32 B ) $.
  ntp4vc-y-valid $e |- NTP4VCValid D ( NTP4VCSigned32 A ) $.
  ntp4vc-q-valid $e
    |- NTP4VCValid E
        ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) + 1 )
  $.
  ntp4vc-nx-valid $e
    |- NTP4VCValid F ( ( NTP4VCSigned32 B ) + 1 )
  $.
  ntp4vc-ny-valid $e |- NTP4VCValid G ( NTP4VCSigned32 A ) $.
  ntp4vc-q-writable $e |- ( NTP4VCWritable E ) = 1 $.
  ntp4vc-x-writable $e |- ( NTP4VCWritable C ) = 1 $.
  ntp4vc-nx-writable $e |- ( NTP4VCWritable F ) = 1 $.
  ntp4vc-ny-writable $e |- ( NTP4VCWritable G ) = 1 $.
  ntp4vc-top-positive $e
    |- 0 < ( NTP4VCPelts D
        ( ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 A ) ) - 1 ) )
  $.
  ntp4vc-o1-forward $e
    |- ( ( NTP4VCSigned32 A ) = 1 -> H = 1 )
  $.
  ntp4vc-o1-backward $e |- ( H = 1 -> A = 1 ) $.

  div-Div-div-qr-in-place-vc $a
    |- NTP4VCVC A B C D E F G H
  $.
$}
