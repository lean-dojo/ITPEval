$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_SubOld_wmpn_sub_in_placeqtvc: the verification
  condition for in-place multiprecision subtraction, including exact 32- and
  64-bit word semantics, pointer validity and metadata, borrow propagation,
  a one-limb modular update, loop invariants, memory framing, and the final
  arithmetic relation. This file contains no proof.

  Pointer values retain an array with a total ZZ-indexed limb map and
  independent nonnegative-integer length metadata, together with integer
  offset and bounds, a writability bit, and an arbitrary nonempty zone.
  The helper predicates below are definitional abbreviations for the source
  validity, value, metadata, functional update, frame, branch,
  loop-invariant, and postcondition formulas. Proposition-valued
  conditionals are rendered as equivalent exhaustive guarded disjunctions.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCSameMeta NTP4VCUpdateLaw NTP4VCBounds
  NTP4VCTailFrame NTP4VCOutsideFrame NTP4VCInvariant NTP4VCFinal
  NTP4VCBoolResult NTP4VCInitialResult NTP4VCO4Branch
  NTP4VCAfterWrite NTP4VCStep NTP4VCLoopBody NTP4VCBorrowCase
  NTP4VCO2Branch NTP4VCContinuation NTP4VCVC
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
ntp4vc-same-meta-syn $a wff NTP4VCSameMeta A B $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-bounds-syn $a wff NTP4VCBounds A B $.
ntp4vc-tail-frame-syn $a wff NTP4VCTailFrame A B C D $.
ntp4vc-outside-frame-syn $a wff NTP4VCOutsideFrame A B C $.
ntp4vc-invariant-syn $a wff NTP4VCInvariant A B C D E F G $.
ntp4vc-final-syn $a wff NTP4VCFinal A B C D E F $.
ntp4vc-bool-result-syn $a wff NTP4VCBoolResult A B $.
ntp4vc-initial-result-syn $a wff NTP4VCInitialResult A B C D E $.
ntp4vc-o4-branch-syn $a wff NTP4VCO4Branch A B C D E F G H I $.
ntp4vc-after-write-syn $a wff NTP4VCAfterWrite A B C D E F G H I $.
ntp4vc-step-syn $a wff NTP4VCStep A B C D E F G H $.
ntp4vc-loop-body-syn $a wff NTP4VCLoopBody A B C D E F G H $.
ntp4vc-borrow-case-syn $a wff NTP4VCBorrowCase A B C D E F G $.
ntp4vc-o2-branch-syn $a wff NTP4VCO2Branch A B C D E F G H $.
ntp4vc-continuation-syn $a wff NTP4VCContinuation A B C D E F $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C D E $.

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
  $d j A B C D $.
  ntp4vc-update-law-def $a
    |- ( NTP4VCUpdateLaw A B C D <->
        A. j e. ZZ
          ( ( NTP4VCPelts B j ) =
            if ( j = C , D , ( NTP4VCPelts A j ) ) ) )
  $.
$}

ntp4vc-bounds-def $a
  |- ( NTP4VCBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A ) ) )
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
      ( ( ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 D ) /\
          ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 F ) ) /\
        ( ( ( NTP4VCValue A ( NTP4VCSigned32 D ) ) -
            ( ( ( 2 ^ ; 6 4 ) ^
                ( NTP4VCToNat ( NTP4VCSigned32 D ) ) ) x. E ) ) =
            ( ( NTP4VCValue B ( NTP4VCSigned32 D ) ) -
              ( NTP4VCValue C ( NTP4VCSigned32 G ) ) ) /\
          ( ( 0 <_ E /\ E <_ 1 ) /\
            ( ( D = F \/ E = 1 ) /\
              ( NTP4VCTailFrame A B
                  ( NTP4VCSigned32 D ) ( NTP4VCSigned32 F ) /\
                NTP4VCOutsideFrame A B
                  ( NTP4VCSigned32 F ) ) ) ) ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C D E F <->
      ( ( ( NTP4VCValue A ( NTP4VCSigned32 D ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 D ) ) ) x. F ) ) =
          ( ( NTP4VCValue B ( NTP4VCSigned32 D ) ) -
            ( NTP4VCValue C ( NTP4VCSigned32 E ) ) ) /\
        ( ( 0 <_ F /\ F <_ 1 ) /\
          NTP4VCOutsideFrame A B ( NTP4VCSigned32 D ) ) ) )
$.

ntp4vc-bool-result-def $a
  |- ( NTP4VCBoolResult A B <->
      ( ( A = 0 -> B = 1 ) /\ ( B = 1 -> A = 0 ) ) )
$.

ntp4vc-initial-result-def $a
  |- ( NTP4VCInitialResult A B C D E <->
      ( ( ( NTP4VCValue A ( NTP4VCSigned32 E ) ) -
          ( ( ( 2 ^ ; 6 4 ) ^
              ( NTP4VCToNat ( NTP4VCSigned32 E ) ) ) x. D ) ) =
          ( ( NTP4VCValue B ( NTP4VCSigned32 E ) ) -
            ( NTP4VCValue C ( NTP4VCSigned32 E ) ) ) /\
        ( ( 0 <_ D /\ D <_ 1 ) /\
          NTP4VCOutsideFrame A B ( NTP4VCSigned32 E ) ) ) )
$.

ntp4vc-o4-branch-def $a
  |- ( NTP4VCO4Branch A B C D E F G H I <->
      ( ( I =/= 1 /\ NTP4VCFinal A B C G H 0 ) \/
        ( I = 1 /\
          ( ( 0 <_ ( ( NTP4VCSigned32 G ) -
                      ( NTP4VCSigned32 D ) ) /\
              ( ( NTP4VCSigned32 G ) -
                ( NTP4VCSigned32 F ) ) <
              ( ( NTP4VCSigned32 G ) -
                ( NTP4VCSigned32 D ) ) ) /\
            NTP4VCInvariant A B C F E G H ) ) ) )
$.

${
  $d x o b A B C D E F G H I $.
  ntp4vc-after-write-def $a
    |- ( NTP4VCAfterWrite A B C D E F G H I <->
        A. x e. ( NTP4VCPtr I )
          ( NTP4VCSameMeta x A ->
            ( ( NTP4VCUpdateLaw A x
                  ( ( NTP4VCOffset x ) +
                    ( NTP4VCSigned32 D ) ) H /\
                ( NTP4VCPelts x
                    ( ( NTP4VCOffset x ) +
                      ( NTP4VCSigned32 D ) ) ) = H ) ->
              ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 D ) + 1 ) /\
                A. o e. NTP4VCWord32
                  ( ( NTP4VCSigned32 o ) =
                      ( ( NTP4VCSigned32 D ) + 1 ) ->
                    A. b e. 2
                      ( NTP4VCBoolResult
                          ( NTP4VCPelts A
                            ( ( NTP4VCOffset A ) +
                              ( NTP4VCSigned32 D ) ) ) b ->
                        NTP4VCO4Branch
                          x B C D E o F G b ) ) ) ) ) )
  $.
$}

${
  $d r A B C D E F G H $.
  ntp4vc-step-def $a
    |- ( NTP4VCStep A B C D E F G H <->
        ( NTP4VCBounds A ( NTP4VCSigned32 D ) /\
          A. r e. NTP4VCWord64
            ( r =
                ( ( ( NTP4VCPelts A
                        ( ( NTP4VCOffset A ) +
                          ( NTP4VCSigned32 D ) ) ) - 1 )
                  mod ( 2 ^ ; 6 4 ) ) ->
              ( ( NTP4VCBounds A ( NTP4VCSigned32 D ) /\
                  ( NTP4VCWritable A ) = 1 ) /\
                NTP4VCAfterWrite A B C D E F G r H ) ) ) )
  $.
$}

ntp4vc-loop-body-def $a
  |- ( NTP4VCLoopBody A B C D E F G H <->
      ( ( ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F ) /\
          NTP4VCStep A B C D E F G H ) \/
        ( ( NTP4VCSigned32 F ) <_ ( NTP4VCSigned32 D ) /\
          NTP4VCFinal A B C F G E ) ) )
$.

${
  $d i b x A B C D E F G $.
  ntp4vc-borrow-case-def $a
    |- ( NTP4VCBorrowCase A B C D E F G <->
        ( NTP4VCInvariant A B C F D E F /\
          A. i e. NTP4VCWord32
            A. b e. NTP4VCWord64
              A. x e. ( NTP4VCPtr G )
                ( NTP4VCSameMeta x A ->
                  ( NTP4VCInvariant x B C i b E F ->
                    NTP4VCLoopBody x B C i b E F G ) ) ) ) )
  $.
$}

ntp4vc-o2-branch-def $a
  |- ( NTP4VCO2Branch A B C D E F G H <->
      ( ( E =/= 1 /\ NTP4VCBorrowCase A B C D F G H ) \/
        ( E = 1 /\ NTP4VCFinal A B C F G D ) ) )
$.

${
  $d o b A B C D E F $.
  ntp4vc-continuation-def $a
    |- ( NTP4VCContinuation A B C D E F <->
        A. o e. NTP4VCWord64
          ( NTP4VCInitialResult A B C o E ->
            A. b e. 2
              ( NTP4VCBoolResult o b ->
                NTP4VCO2Branch A B C o b D E F ) ) ) )
  $.
$}

${
  $d x A B C D E $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D E <->
        ( NTP4VCValid A ( NTP4VCSigned32 D ) /\
          ( NTP4VCValid B ( NTP4VCSigned32 D ) /\
            ( ( NTP4VCWritable A ) = 1 /\
              A. x e. ( NTP4VCPtr E )
                ( NTP4VCSameMeta x A ->
                  NTP4VCContinuation x A B C D E ) ) ) ) )
  $.
$}

${
  $( Source theorem parameters: A=sy, B=sx, C=x, D=y, with zone Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-sy-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-x-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-sy-nonnegative $e |- 0 <_ ( NTP4VCSigned32 A ) $.
  ntp4vc-length-order $e
    |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B )
  $.
  ntp4vc-x-valid $e |- NTP4VCValid C ( NTP4VCSigned32 B ) $.
  ntp4vc-y-valid $e |- NTP4VCValid D ( NTP4VCSigned32 A ) $.
  ntp4vc-x-writable $e |- ( NTP4VCWritable C ) = 1 $.

  ntp4vc-wmpn-sub-in-place-statement $a
    |- NTP4VCVC C D B A Z
  $.
$}
