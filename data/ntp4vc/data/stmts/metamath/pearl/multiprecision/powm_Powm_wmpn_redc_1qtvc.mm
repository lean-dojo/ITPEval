$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_wmpn_redc_1qtvc: the verification
  condition for one-limb Montgomery reduction of a writable
  multiprecision integer, including the reduction loop, limb updates,
  conditional subtraction, framing, congruence, and output bound.
  This file contains no proof.

  Words use their complete canonical integer carriers.  A pointer retains
  the source finite limb sequence, integer offset and bounds, Boolean
  writability field, and arbitrary nonempty zone.  Lookup is totalized
  through the source Int.toNat conversion, and value is the exact
  little-endian radix-2^64 finite sum.  All helper predicates below are
  bidirectional definitional factorizations of the generated verification
  condition; in particular, no loop invariant, branch, update, or framing
  obligation is omitted.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCIPow NTP4VCOdd NTP4VCPeltsEq NTP4VCShiftCopy
  NTP4VCMetaEq NTP4VCPair NTP4VCClosedBounds NTP4VCOpenBounds
  NTP4VCOutside NTP4VCUpdateLaw NTP4VCCoreInv NTP4VCRedc
  NTP4VCResultCore NTP4VCElseCore NTP4VCFinalCore NTP4VCThenBranch
  NTP4VCBoolStage NTP4VCO6Stage NTP4VCOutputStage NTP4VCBackStage
  NTP4VCCleanup NTP4VCWriteStage NTP4VCMulStage NTP4VCIteration
  NTP4VCInitialBranch NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn $a wff NTP4VCInt32InBounds A $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-ipow-syn $a class ( NTP4VCIPow A B ) $.
ntp4vc-odd-syn $a wff NTP4VCOdd A $.
ntp4vc-pelts-eq-syn $a wff NTP4VCPeltsEq A B $.
ntp4vc-shift-copy-syn $a wff NTP4VCShiftCopy A B C $.
ntp4vc-meta-eq-syn $a wff NTP4VCMetaEq A B $.
ntp4vc-pair-syn $a wff NTP4VCPair A B C $.
ntp4vc-closed-bounds-syn $a wff NTP4VCClosedBounds A B $.
ntp4vc-open-bounds-syn $a wff NTP4VCOpenBounds A $.
ntp4vc-outside-syn $a wff NTP4VCOutside A B C $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-core-inv-syn $a wff NTP4VCCoreInv A B C D E F G $.
ntp4vc-redc-syn $a wff NTP4VCRedc A B C D $.
ntp4vc-result-core-syn $a wff NTP4VCResultCore A B C D E F $.
ntp4vc-else-core-syn $a wff NTP4VCElseCore A B C D E $.
ntp4vc-final-core-syn $a wff NTP4VCFinalCore A B C D E $.
ntp4vc-then-branch-syn
  $a wff NTP4VCThenBranch A B C D E F G H $.
ntp4vc-bool-stage-syn
  $a wff NTP4VCBoolStage A B C D E F G H I J $.
ntp4vc-o6-stage-syn
  $a wff NTP4VCO6Stage A B C D E F G H I $.
ntp4vc-output-stage-syn
  $a wff NTP4VCOutputStage A B C D E F G H $.
ntp4vc-back-stage-syn
  $a wff NTP4VCBackStage A B C D E F G $.
ntp4vc-cleanup-syn
  $a wff NTP4VCCleanup A B C D E F G $.
ntp4vc-write-stage-syn
  $a wff NTP4VCWriteStage A B C D E F G H I J $.
ntp4vc-mul-stage-syn
  $a wff NTP4VCMulStage A B C D E F G H I J K $.
ntp4vc-iteration-syn
  $a wff NTP4VCIteration A B C D E F G H I J $.
ntp4vc-initial-branch-syn
  $a wff NTP4VCInitialBranch A B C D E F G H I $.
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
      ( ( Word NTP4VCWord64 ) X.
        ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) ) )
$.

ntp4vc-data-def $a |- ( NTP4VCData A ) = ( 1st ` A ) $.
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
      if ( ( NTP4VCToNat B ) < ( # ` ( NTP4VCData A ) ) ,
           ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
           0 )
$.

ntp4vc-valid-def $a
  |- ( NTP4VCValid A B <->
      ( NTP4VCInt32InBounds B /\
        ( 0 <_ B /\
          ( ( 0 <_ ( NTP4VCMin A ) /\
              ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) ) /\
            ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
              ( NTP4VCMax A ) <_ ( # ` ( NTP4VCData A ) ) ) ) ) ) )
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

ntp4vc-ipow-def $a
  |- ( NTP4VCIPow A B ) = ( A ^ ( NTP4VCToNat B ) )
$.

${
  $d q A $.
  ntp4vc-odd-def $a
    |- ( NTP4VCOdd A <-> E. q e. ZZ ( A = ( ( 2 x. q ) + 1 ) ) )
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
        ( ( # ` ( NTP4VCData A ) ) = ( # ` ( NTP4VCData B ) ) /\
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
      ( ( # ` ( NTP4VCData A ) ) = ( # ` ( NTP4VCData B ) ) /\
        ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
                ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) ) ) )
$.

ntp4vc-pair-def $a
  |- ( NTP4VCPair A B C <->
      ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
        ( ( # ` ( NTP4VCData B ) ) = ( # ` ( NTP4VCData C ) ) /\
          ( ( NTP4VCOffset A ) = ( NTP4VCOffset C ) /\
            ( ( NTP4VCMin A ) = ( NTP4VCMin C ) /\
              ( ( NTP4VCMax A ) = ( NTP4VCMax C ) /\
                ( ( NTP4VCWritable A ) = ( NTP4VCWritable C ) /\
                  ( NTP4VCZone A ) = ( NTP4VCZone C ) ) ) ) ) ) ) )
$.

ntp4vc-closed-bounds-def $a
  |- ( NTP4VCClosedBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) ) )
$.

ntp4vc-open-bounds-def $a
  |- ( NTP4VCOpenBounds A <->
      ( ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) /\
        ( NTP4VCOffset A ) < ( NTP4VCMax A ) ) )
$.

${
  $d j A B C $.
  ntp4vc-outside-def $a
    |- ( NTP4VCOutside A B C <->
        A. j e. ZZ
          ( ( j < ( NTP4VCOffset A ) \/
              ( ( NTP4VCOffset A ) + C ) <_ j ) ->
            ( NTP4VCPelts A j ) = ( NTP4VCPelts B j ) ) )
  $.
$}

${
  $d j A B C D $.
  ntp4vc-update-law-def $a
    |- ( NTP4VCUpdateLaw A B C D <->
        A. j e. ZZ
          ( ( NTP4VCPelts B j ) =
            if ( j = C , D , ( NTP4VCPelts A j ) ) ) )
  $.
$}

ntp4vc-core-inv-def $a
  |- ( NTP4VCCoreInv A B C D E F G <->
      ( ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + F ) /\
        ( NTP4VCPeltsEq A B /\
          ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
            ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
              ( ( # ` ( NTP4VCData A ) ) =
                  ( # ` ( NTP4VCData B ) ) /\
                ( ( NTP4VCWritable A ) = 1 /\
                  ( ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) F ) x.
                        ( NTP4VCValue A ( ( D + D ) - F ) ) ) +
                      ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) D ) x.
                        ( NTP4VCValue B F ) ) =
                    ( ( NTP4VCValue C ( D + D ) ) + ( E x. G ) ) /\
                    ( ( 0 <_ G /\
                        G < ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) F ) ) /\
                      ( ( ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) F ) x.
                              ( NTP4VCValue A ( ( D + D ) - F ) ) ) +
                            ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) D ) x.
                              ( NTP4VCValue B F ) ) )
                          mod E ) =
                        ( ( NTP4VCValue C ( D + D ) ) mod E ) ) ) ) ) ) ) ) ) ) )
$.

ntp4vc-redc-def $a
  |- ( NTP4VCRedc A B C D <->
      ( ( A mod D ) =
        ( ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) C ) x. B ) mod D ) ) )
$.

ntp4vc-result-core-def $a
  |- ( NTP4VCResultCore A B C D E F <->
      ( ( ( NTP4VCValue A D ) mod E ) =
          ( ( ( NTP4VCValue B D ) +
              ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) D ) x. F ) )
            mod E ) /\
        ( NTP4VCOutside A B D /\
          ( ( NTP4VCValue C ( 2 x. D ) ) <
              ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) D ) x. E ) ->
            ( NTP4VCValue A D ) < ( 2 x. E ) ) ) ) )
$.

ntp4vc-else-core-def $a
  |- ( NTP4VCElseCore A B C D E <->
      ( ( ( NTP4VCValue A C ) mod D ) =
          ( ( ( NTP4VCValue A C ) +
              ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) C ) x. E ) )
            mod D ) /\
        ( ( NTP4VCValue B ( 2 x. C ) ) <
            ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) C ) x. D ) ->
          ( NTP4VCValue A C ) < ( 2 x. D ) ) ) )
$.

ntp4vc-final-core-def $a
  |- ( NTP4VCFinalCore A B C D E <->
      ( NTP4VCRedc
          ( NTP4VCValue C ( 2 x. E ) )
          ( NTP4VCValue A E ) E
          ( NTP4VCValue D E ) /\
        ( NTP4VCOutside A B E /\
          ( ( NTP4VCValue C ( 2 x. E ) ) <
              ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) E ) x.
                ( NTP4VCValue D E ) ) ->
            ( NTP4VCValue A E ) <
              ( 2 x. ( NTP4VCValue D E ) ) ) ) ) )
$.

${
  $d r b A B C D E F G H $.
  ntp4vc-then-branch-def $a
    |- ( NTP4VCThenBranch A B C D E F G H <->
        ( ( 0 <_ A /\
            ( NTP4VCValid F A /\
              ( NTP4VCValid B A /\
                ( NTP4VCWritable F ) = 1 ) ) ) /\
          A. r e. ( NTP4VCPtr H )
            ( NTP4VCMetaEq r F ->
              A. b e. NTP4VCWord64
                ( ( ( NTP4VCValue r A ) -
                      ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) A ) x. b ) =
                    ( ( NTP4VCValue F A ) -
                      ( NTP4VCValue B A ) ) /\
                    ( ( 0 <_ b /\ b <_ 1 ) /\
                      NTP4VCOutside r F A ) ) ->
                  NTP4VCResultCore r F C A E G ) ) ) )
  $.
$}

${
  $d r A B C D E F G H I J $.
  ntp4vc-bool-stage-def $a
    |- ( NTP4VCBoolStage A B C D E F G H I J <->
        ( ( I = 0 -> NTP4VCThenBranch A B C D E F G J ) /\
          ( ( I = 1 -> NTP4VCElseCore F C A E G ) /\
            A. r e. ( NTP4VCPtr J )
              ( NTP4VCMetaEq r F ->
                ( NTP4VCResultCore r F C A E G ->
                  NTP4VCFinalCore r D C B A ) ) ) ) )
  $.
$}

${
  $d o b A B C D E F G H I $.
  ntp4vc-o6-stage-def $a
    |- ( NTP4VCO6Stage A B C D E F G H I <->
        A. o e. NTP4VCWord64
          ( ( ( ( 0 <_ o /\ o <_ 1 ) /\
                ( ( NTP4VCValue H A ) +
                    ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) A ) x. o ) =
                  ( ( NTP4VCValue F A ) +
                    ( NTP4VCValue G A ) ) ) /\
              NTP4VCOutside H D A ) ->
            A. b e. { 0 , 1 }
              ( ( ( o = 0 -> b = 1 ) /\
                  ( b = 1 -> o = 0 ) ) ->
                NTP4VCBoolStage A B C D E H o F b I ) ) )
  $.
$}

${
  $d r A B C D E F G H $.
  ntp4vc-output-stage-def $a
    |- ( NTP4VCOutputStage A B C D E F G H <->
        ( ( NTP4VCValid F A /\
            ( NTP4VCValid G A /\
              ( NTP4VCValid D A /\
                ( NTP4VCWritable D ) = 1 ) ) ) /\
          A. r e. ( NTP4VCPtr H )
            ( NTP4VCMetaEq r D ->
              NTP4VCO6Stage A B C D E F G r H ) ) )
  $.
$}

${
  $d o p A B C D E F G $.
  ntp4vc-back-stage-def $a
    |- ( NTP4VCBackStage A B C D E F G <->
        ( NTP4VCInt32InBounds ( -u A ) /\
          A. o e. NTP4VCWord32
            ( ( NTP4VCSigned32 o ) = ( -u A ) ->
              ( NTP4VCClosedBounds F ( NTP4VCSigned32 o ) /\
                A. p e. ( NTP4VCPtr G )
                  ( NTP4VCShiftCopy p F ( NTP4VCSigned32 o ) ->
                    NTP4VCOutputStage A B C D E F p G ) ) ) ) )
  $.
$}

${
  $d o p A B C D E F G $.
  ntp4vc-cleanup-def $a
    |- ( NTP4VCCleanup A B C D E F G <->
        ( NTP4VCInt32InBounds ( -u A ) /\
          A. o e. NTP4VCWord32
            ( ( NTP4VCSigned32 o ) = ( -u A ) ->
              ( NTP4VCClosedBounds F ( NTP4VCSigned32 o ) /\
                A. p e. ( NTP4VCPtr G )
                  ( NTP4VCShiftCopy p F ( NTP4VCSigned32 o ) ->
                    NTP4VCBackStage A B C D E F G ) ) ) ) )
  $.
$}

${
  $d p q r A B C D E F G H I J $.
  ntp4vc-write-stage-def $a
    |- ( NTP4VCWriteStage A B C D E F G H I J <->
        A. p e. ( NTP4VCPtr J )
          A. q e. ( NTP4VCPtr J )
            ( NTP4VCPair p q G ->
              ( NTP4VCPair p q G ->
                ( NTP4VCMetaEq q H ->
                  ( NTP4VCUpdateLaw G p ( NTP4VCOffset p ) I ->
                    ( NTP4VCClosedBounds p 1 /\
                      A. r e. ( NTP4VCPtr J )
                        ( NTP4VCShiftCopy r p 1 ->
                          NTP4VCCoreInv r q B A C
                            ( D + 1 )
                            ( E +
                              ( F x.
                                ( NTP4VCIPow
                                  ( ( 2 ^ ; 6 4 ) ) D ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d o A B C D E F G H I J K $.
  ntp4vc-mul-stage-def $a
    |- ( NTP4VCMulStage A B C D E F G H I J K <->
        A. o e. NTP4VCWord64
          ( ( ( NTP4VCValue I A ) +
                ( ( NTP4VCIPow ( ( 2 ^ ; 6 4 ) ) A ) x. o ) =
              ( ( NTP4VCValue H A ) +
                ( ( NTP4VCValue B A ) x. G ) ) /\
              NTP4VCOutside I H A ) ->
            ( ( NTP4VCOpenBounds I /\
                ( NTP4VCWritable I ) = 1 ) /\
              NTP4VCWriteStage A C D E F G I J o K ) ) )
  $.
$}

${
  $d m o p q r A B C D E F G H I J $.
  ntp4vc-iteration-def $a
    |- ( NTP4VCIteration A B C D E F G H I J <->
        A. m e. NTP4VCWord64
          ( m =
              ( ( ( NTP4VCPelts F ( NTP4VCOffset F ) ) x. D )
                mod ( 2 ^ ; 6 4 ) ) ->
            ( NTP4VCInt32InBounds ( A + A ) /\
              A. o e. NTP4VCWord32
                ( ( NTP4VCSigned32 o ) = ( A + A ) ->
                  ( NTP4VCInt32InBounds
                        ( ( NTP4VCSigned32 o ) -
                          ( NTP4VCSigned32 G ) ) /\
                    A. p e. NTP4VCWord32
                      ( ( NTP4VCSigned32 p ) =
                          ( ( NTP4VCSigned32 o ) -
                            ( NTP4VCSigned32 G ) ) ->
                        ( ( NTP4VCValid B A /\
                            ( NTP4VCValid F A /\
                              ( NTP4VCWritable F ) = 1 ) ) /\
                          A. q e. ( NTP4VCPtr J )
                            A. r e. ( NTP4VCPtr J )
                              ( NTP4VCPair q r F ->
                                ( NTP4VCPair q r F ->
                                  ( NTP4VCMetaEq r I ->
                                    NTP4VCMulStage A B C E
                                      ( NTP4VCSigned32 G ) H m
                                      F q r J ) ) ) ) ) ) ) ) ) )
  $.
$}

${
  $d a j p q A B C D E F G H I $.
  ntp4vc-initial-branch-def $a
    |- ( NTP4VCInitialBranch A B C D E F G H I <->
        ( NTP4VCCoreInv F C C A H 0 0 /\
          A. a e. ZZ
            A. p e. ( NTP4VCPtr I )
              A. q e. ( NTP4VCPtr I )
                ( NTP4VCMetaEq q C ->
                  ( ( A. j e. NTP4VCWord32
                        ( ( ( 0 <_ ( NTP4VCSigned32 j ) /\
                              ( NTP4VCSigned32 j ) <_
                                ( NTP4VCSigned32 G ) ) /\
                            NTP4VCCoreInv p q C A H
                              ( NTP4VCSigned32 j ) a ) ->
                          ( NTP4VCOpenBounds p /\
                            NTP4VCIteration A B C E H
                              p j a q I ) ) ) /\
                      ( NTP4VCCoreInv p q C A H
                          ( ( NTP4VCSigned32 G ) + 1 ) a ->
                        NTP4VCCleanup A B C D H p I ) ) ) ) ) )
  $.
$}

${
  $d o g A B C D E F $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D E F <->
        ( NTP4VCClosedBounds C 0 /\
          A. o e. ( NTP4VCPtr F )
            ( NTP4VCShiftCopy o C 0 ->
              ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 A ) - 1 ) /\
                A. g e. NTP4VCWord32
                  ( ( NTP4VCSigned32 g ) =
                      ( ( NTP4VCSigned32 A ) - 1 ) ->
                    ( ( ( 0 <_
                            ( ( NTP4VCSigned32 g ) + 1 ) ) ->
                        NTP4VCInitialBranch
                          ( NTP4VCSigned32 A ) B C D E
                          o g ( NTP4VCValue B
                            ( NTP4VCSigned32 A ) ) F ) /\
                      ( ( ( NTP4VCSigned32 g ) + 1 ) < 0 ->
                        NTP4VCCleanup
                          ( NTP4VCSigned32 A ) B C D
                          ( NTP4VCValue B
                            ( NTP4VCSigned32 A ) )
                          o F ) ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-n-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-mp-type $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-up-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-rp-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-invm-type $e |- E e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- 0 < ( NTP4VCSigned32 A ) $.
  ntp4vc-fact1 $e |- NTP4VCValid B ( NTP4VCSigned32 A ) $.
  ntp4vc-fact2 $e
    |- NTP4VCValid C ( 2 x. ( NTP4VCSigned32 A ) )
  $.
  ntp4vc-fact3 $e |- NTP4VCValid D ( NTP4VCSigned32 A ) $.
  ntp4vc-fact4 $e
    |- NTP4VCOdd ( NTP4VCValue B ( NTP4VCSigned32 A ) )
  $.
  ntp4vc-fact5 $e
    |- ( ( ( NTP4VCValue B ( NTP4VCSigned32 A ) ) x. E )
         mod ( 2 ^ ; 6 4 ) ) =
       ( ( 2 ^ ; 6 4 ) - 1 )
  $.
  ntp4vc-fact6 $e |- ( NTP4VCWritable C ) = 1 $.
  ntp4vc-fact7 $e |- ( NTP4VCWritable D ) = 1 $.

  ntp4vc-wmpn-redc-1-statement $a
    |- NTP4VCVC A B C D E Z
  $.
$}
