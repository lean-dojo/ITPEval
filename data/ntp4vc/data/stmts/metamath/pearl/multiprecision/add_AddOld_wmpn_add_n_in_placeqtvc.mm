$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/add_AddOld_wmpn_add_n_in_placeqtvc: the verification
  condition for in-place equal-length multiprecision addition, including
  exact 32- and 64-bit word semantics, pointer validity and metadata, carry
  propagation, one-limb functional update, loop invariants, memory framing,
  and the final arithmetic relation. This file contains no proof.

  Pointer values retain an array with a total ZZ-indexed limb map and
  independent nonnegative-integer length metadata, together with integer
  offset and bounds, a writability bit, and an arbitrary nonempty zone.
  The helper predicates below are definitional abbreviations for the source
  validity, value, metadata, update, frame, invariant, branch, and complete
  verification-condition formulas.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCSameMeta NTP4VCUpdateLaw NTP4VCBounds
  NTP4VCTailFrame NTP4VCOutsideFrame NTP4VCInvariant NTP4VCFinal
  NTP4VCNext NTP4VCAfterWrite NTP4VCThenBranch NTP4VCLoopBody
  NTP4VCVC
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
ntp4vc-invariant-syn $a wff NTP4VCInvariant A B C D E F $.
ntp4vc-final-syn $a wff NTP4VCFinal A B C D E $.
ntp4vc-next-syn $a wff NTP4VCNext A B C D E F G $.
ntp4vc-after-write-syn $a wff NTP4VCAfterWrite A B C D E F G H I $.
ntp4vc-then-branch-syn $a wff NTP4VCThenBranch A B C D E F G $.
ntp4vc-loop-body-syn $a wff NTP4VCLoopBody A B C D E F G $.
ntp4vc-vc-syn $a wff NTP4VCVC A B C D $.

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
  |- ( NTP4VCInvariant A B C D E F <->
      ( ( 0 <_ ( NTP4VCSigned32 D ) /\
          ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 F ) ) /\
        ( ( ( NTP4VCValue A ( NTP4VCSigned32 D ) ) +
            ( ( ( 2 ^ ; 6 4 ) ^
                ( NTP4VCToNat ( NTP4VCSigned32 D ) ) ) x. E ) ) =
            ( ( NTP4VCValue B ( NTP4VCSigned32 D ) ) +
              ( NTP4VCValue C ( NTP4VCSigned32 D ) ) ) /\
          ( ( 0 <_ E /\ E <_ 1 ) /\
            ( NTP4VCTailFrame A B
                ( NTP4VCSigned32 D ) ( NTP4VCSigned32 F ) /\
              NTP4VCOutsideFrame A B
                ( NTP4VCSigned32 F ) ) ) ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C D E <->
      ( ( 0 <_ D /\ D <_ 1 ) /\
        ( ( ( NTP4VCValue A ( NTP4VCSigned32 E ) ) +
            ( ( ( 2 ^ ; 6 4 ) ^
                ( NTP4VCToNat ( NTP4VCSigned32 E ) ) ) x. D ) ) =
            ( ( NTP4VCValue B ( NTP4VCSigned32 E ) ) +
              ( NTP4VCValue C ( NTP4VCSigned32 E ) ) ) /\
          NTP4VCOutsideFrame A B ( NTP4VCSigned32 E ) ) ) )
$.

ntp4vc-next-def $a
  |- ( NTP4VCNext A B C D E F G <->
      ( ( 0 <_ ( ( NTP4VCSigned32 G ) -
                  ( NTP4VCSigned32 F ) ) /\
          ( ( NTP4VCSigned32 G ) -
            ( NTP4VCSigned32 D ) ) <
          ( ( NTP4VCSigned32 G ) -
            ( NTP4VCSigned32 F ) ) ) /\
        NTP4VCInvariant A B C D E G ) )
$.

${
  $d x o A B C D E F G H I $.
  ntp4vc-after-write-def $a
    |- ( NTP4VCAfterWrite A B C D E F G H I <->
        A. x e. ( NTP4VCPtr I )
          ( NTP4VCSameMeta x A ->
            ( ( NTP4VCUpdateLaw A x
                  ( ( NTP4VCOffset x ) +
                    ( NTP4VCSigned32 D ) ) F /\
                ( NTP4VCPelts x
                    ( ( NTP4VCOffset x ) +
                      ( NTP4VCSigned32 D ) ) ) = F ) ->
              ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 D ) + 1 ) /\
                A. o e. NTP4VCWord32
                  ( ( NTP4VCSigned32 o ) =
                      ( ( NTP4VCSigned32 D ) + 1 ) ->
                    NTP4VCNext x B C o G D H ) ) ) ) )
  $.
$}

${
  $d r c A B C D E F G $.
  ntp4vc-then-branch-def $a
    |- ( NTP4VCThenBranch A B C D E F G <->
        ( NTP4VCBounds A ( NTP4VCSigned32 D ) /\
          ( NTP4VCBounds C ( NTP4VCSigned32 D ) /\
            ( ( 0 <_ E /\ E <_ 1 ) /\
              A. r e. NTP4VCWord64
                A. c e. NTP4VCWord64
                  ( ( ( r + ( ( 2 ^ ; 6 4 ) x. c ) ) =
                        ( ( NTP4VCPelts A
                              ( ( NTP4VCOffset A ) +
                                ( NTP4VCSigned32 D ) ) ) +
                          ( ( NTP4VCPelts C
                                ( ( NTP4VCOffset C ) +
                                  ( NTP4VCSigned32 D ) ) ) + E ) ) /\
                      ( 0 <_ c /\ c <_ 1 ) ) ->
                    ( ( NTP4VCBounds A ( NTP4VCSigned32 D ) /\
                        ( NTP4VCWritable A ) = 1 ) /\
                      NTP4VCAfterWrite
                        A B C D E r c F G ) ) ) ) ) ) )
  $.
$}

ntp4vc-loop-body-def $a
  |- ( NTP4VCLoopBody A B C D E F G <->
      ( ( ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F ) /\
          NTP4VCThenBranch A B C D E F G ) \/
        ( ( NTP4VCSigned32 F ) <_ ( NTP4VCSigned32 D ) /\
          NTP4VCFinal A B C E F ) ) )
$.

${
  $d i c x A B C D $.
  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D <->
        ( 0 <_ 0 /\
          ( 0 <_ ( NTP4VCSigned32 C ) /\
            ( ( ( NTP4VCValue A 0 ) +
                ( ( ( 2 ^ ; 6 4 ) ^ 0 ) x. 0 ) ) =
                ( ( NTP4VCValue A 0 ) + ( NTP4VCValue B 0 ) ) /\
              ( 0 <_ 0 /\
                ( 0 <_ 1 /\
                  A. i e. NTP4VCWord32
                    A. c e. NTP4VCWord64
                      A. x e. ( NTP4VCPtr D )
                        ( NTP4VCSameMeta x A ->
                          ( NTP4VCInvariant x A B i c C ->
                            NTP4VCLoopBody
                              x A B i c C D ) ) ) ) ) ) ) ) )
  $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- C e. NTP4VCWord32 $.
  ntp4vc-y-type $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-x-valid $e |- NTP4VCValid A ( NTP4VCSigned32 C ) $.
  ntp4vc-y-valid $e |- NTP4VCValid B ( NTP4VCSigned32 C ) $.
  ntp4vc-x-writable $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-add-n-in-place-statement $a
    |- NTP4VCVC A B C Z
  $.
$}
