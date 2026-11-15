$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/add_1_Add_1_wmpn_add_1_in_placeqtvc:
  verification conditions for adding one machine limb in place to a writable
  multiprecision integer, including carry propagation, memory framing, signed
  32-bit indexing, and the final arithmetic relation.  This file contains no
  proof.

  A source pointer record retains a total integer-indexed limb map with an
  independent nonnegative length, offset, minimum and maximum bounds,
  writability bit, and arbitrary nonempty zone carrier.  The helper predicates
  below are definitional abbreviations for the source validity, value, frame,
  loop-invariant, update, and postcondition formulas.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCPeltsMap
  NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts NTP4VCValid
  NTP4VCValue NTP4VCBounds NTP4VCSameMeta NTP4VCUpdateLaw
  NTP4VCFrame NTP4VCInvariant NTP4VCFinal NTP4VCBoolResult
  NTP4VCO3Branch NTP4VCAfterWrite NTP4VCStep NTP4VCLoopBody
  NTP4VCCarryCase NTP4VCInitialWrite NTP4VCVC
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
ntp4vc-bounds-syn $a wff NTP4VCBounds A B $.
ntp4vc-same-meta-syn $a wff NTP4VCSameMeta A B $.
ntp4vc-update-law-syn $a wff NTP4VCUpdateLaw A B C D $.
ntp4vc-frame-syn $a wff NTP4VCFrame A B C $.
ntp4vc-invariant-syn $a wff NTP4VCInvariant A B C D E F $.
ntp4vc-final-syn $a wff NTP4VCFinal A B C D E $.
ntp4vc-bool-result-syn $a wff NTP4VCBoolResult A B $.
ntp4vc-o3-branch-syn $a wff NTP4VCO3Branch A B C D E F G H I $.
ntp4vc-after-write-syn $a wff NTP4VCAfterWrite A B C D E F G H $.
ntp4vc-step-syn $a wff NTP4VCStep A B C D E F G $.
ntp4vc-loop-body-syn $a wff NTP4VCLoopBody A B C D E F G $.
ntp4vc-carry-case-syn $a wff NTP4VCCarryCase A B C D E $.
ntp4vc-initial-write-syn $a wff NTP4VCInitialWrite A B C D $.
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

ntp4vc-bounds-def $a
  |- ( NTP4VCBounds A B <->
      ( ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
        ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A ) ) )
$.

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

ntp4vc-invariant-def $a
  |- ( NTP4VCInvariant A B C D E F <->
      ( ( 1 <_ ( NTP4VCSigned32 C ) /\
          ( NTP4VCSigned32 C ) <_ ( NTP4VCSigned32 E ) ) /\
        ( ( 0 <_ D /\ D <_ 1 ) /\
          ( ( D = 1 \/ C = E ) /\
            ( ( ( NTP4VCValue A ( NTP4VCSigned32 C ) ) +
                ( ( ( 2 ^ ; 6 4 ) ^ ( NTP4VCSigned32 C ) ) x. D ) ) =
              ( ( NTP4VCValue B ( NTP4VCSigned32 C ) ) + F ) /\
              NTP4VCFrame A B ( NTP4VCSigned32 C ) ) ) ) ) )
$.

ntp4vc-final-def $a
  |- ( NTP4VCFinal A B C D E <->
      ( ( ( NTP4VCValue A ( NTP4VCSigned32 C ) ) +
          ( ( ( 2 ^ ; 6 4 ) ^ ( NTP4VCSigned32 C ) ) x. E ) ) =
        ( ( NTP4VCValue B ( NTP4VCSigned32 C ) ) + D ) /\
        ( ( 0 <_ E /\ E <_ 1 ) /\
          NTP4VCFrame A B ( NTP4VCSigned32 C ) ) ) )
$.

ntp4vc-bool-result-def $a
  |- ( NTP4VCBoolResult A B <->
      ( ( A = 0 -> B = 1 ) /\ ( B = 1 -> A = 0 ) ) )
$.

ntp4vc-o3-branch-def $a
  |- ( NTP4VCO3Branch A B C D E F G H I <->
      ( ( I =/= 1 /\ NTP4VCFinal A B F G 0 ) \/
        ( I = 1 /\
          ( ( 0 <_ ( ( NTP4VCSigned32 F ) -
                      ( NTP4VCSigned32 C ) ) /\
              ( ( NTP4VCSigned32 F ) -
                ( NTP4VCSigned32 E ) ) <
              ( ( NTP4VCSigned32 F ) -
                ( NTP4VCSigned32 C ) ) ) /\
            NTP4VCInvariant A B E D F G ) ) ) )
$.

${
  $d x o b A B C D E F G H $.
  ntp4vc-after-write-def $a
    |- ( NTP4VCAfterWrite A B C D E F G H <->
        A. x e. ( NTP4VCPtr G )
          ( NTP4VCSameMeta x A ->
            ( ( NTP4VCUpdateLaw A x
                  ( ( NTP4VCOffset x ) + ( NTP4VCSigned32 C ) ) H /\
                ( NTP4VCPelts x
                    ( ( NTP4VCOffset x ) + ( NTP4VCSigned32 C ) ) ) = H ) ->
              ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 C ) + 1 ) /\
                A. o e. NTP4VCWord32
                  ( ( NTP4VCSigned32 o ) =
                      ( ( NTP4VCSigned32 C ) + 1 ) ->
                    A. b e. { 0 , 1 }
                      ( NTP4VCBoolResult H b ->
                        NTP4VCO3Branch
                          x B C D o E F H b ) ) ) ) ) )
  $.
$}

${
  $d r A B C D E F G $.
  ntp4vc-step-def $a
    |- ( NTP4VCStep A B C D E F G <->
        ( NTP4VCBounds A ( NTP4VCSigned32 C ) /\
          A. r e. NTP4VCWord64
            ( r =
                ( ( ( NTP4VCPelts A
                        ( ( NTP4VCOffset A ) +
                          ( NTP4VCSigned32 C ) ) ) + 1 )
                  mod ( 2 ^ ; 6 4 ) ) ->
              ( ( NTP4VCBounds A ( NTP4VCSigned32 C ) /\
                  ( NTP4VCWritable A ) = 1 ) /\
                NTP4VCAfterWrite A B C D E F G r ) ) ) )
  $.
$}

ntp4vc-loop-body-def $a
  |- ( NTP4VCLoopBody A B C D E F G <->
      ( ( ( NTP4VCSigned32 C ) < ( NTP4VCSigned32 E ) /\
          NTP4VCStep A B C D E F G ) \/
        ( ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 C ) /\
          NTP4VCFinal A B E F D ) ) )
$.

${
  $d o b x A B C D E $.
  ntp4vc-carry-case-def $a
    |- ( NTP4VCCarryCase A B C D E <->
        ( NTP4VCInvariant A B 1 1 C D /\
          A. o e. NTP4VCWord32
            A. b e. NTP4VCWord64
              A. x e. ( NTP4VCPtr E )
                ( NTP4VCSameMeta x A ->
                  ( NTP4VCInvariant x B o b C D ->
                    NTP4VCLoopBody x B o b C D E ) ) ) )
  $.
$}

${
  $d r x A B C D $.
  ntp4vc-initial-write-def $a
    |- ( NTP4VCInitialWrite A B C D <->
        A. r e. NTP4VCWord64
          ( r =
              ( ( ( NTP4VCPelts A ( NTP4VCOffset A ) ) + C )
                mod ( 2 ^ ; 6 4 ) ) ->
            ( ( NTP4VCBounds A 0 /\ ( NTP4VCWritable A ) = 1 ) /\
              A. x e. ( NTP4VCPtr D )
                ( NTP4VCSameMeta x A ->
                  ( NTP4VCUpdateLaw A x ( NTP4VCOffset x ) r ->
                    ( ( r < ( NTP4VCPelts A ( NTP4VCOffset A ) ) /\
                        NTP4VCCarryCase x A B C D ) \/
                      ( ( NTP4VCPelts A ( NTP4VCOffset A ) ) <_ r /\
                        NTP4VCFinal x A B C 0 ) ) ) ) ) ) )
  $.
$}

ntp4vc-vc-def $a
  |- ( NTP4VCVC A B C D <->
      ( ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) /\
        ( ( NTP4VCOffset A ) < ( NTP4VCMax A ) /\
          NTP4VCInitialWrite A B C D ) ) )
$.

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-y-type $e |- C e. NTP4VCWord64 $.
  ntp4vc-valid-hyp $e |- NTP4VCValid A ( NTP4VCSigned32 B ) $.
  ntp4vc-positive-hyp $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-writable-hyp $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-add-1-in-place-statement $a
    |- NTP4VCVC A B C Z
  $.
$}
