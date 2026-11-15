$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_tdiv_qr_in_placeqtvc: the verification
  condition for allocating temporary multiprecision buffers and invoking
  in-place quotient-and-remainder division, including exact word arithmetic,
  pointer validity and allocation metadata, null-zone checks, framing, and
  the final Euclidean quotient-remainder relation. This file contains no proof.

  Source 32- and 64-bit words are represented by their complete unsigned
  integer carriers, with exact two's-complement signed interpretation for
  32-bit words. A pointer retains the Why3 array's total integer-indexed limb
  map, independent nonnegative length, offset and bounds, writability, and an
  arbitrary nonempty zone. The helper predicates below are definitional
  abbreviations for the source validity, value, allocation, metadata, nested
  quantifier, implication, and postcondition formulas.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32
  NTP4VCInt32InBounds NTP4VCUInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCPlength
  NTP4VCOffset NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone
  NTP4VCToNat NTP4VCPelts NTP4VCValid NTP4VCValue
  NTP4VCIsNotNull NTP4VCMallocShape NTP4VCSameMeta
  NTP4VCReleasedShape NTP4VCFinal NTP4VCCorePre
  NTP4VCPostObligation NTP4VCAfterNy NTP4VCAfterNx
  NTP4VCAfterO2 NTP4VCAfterO1 NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn
  $a wff NTP4VCInt32InBounds A $.
ntp4vc-uint32-in-bounds-syn
  $a wff NTP4VCUInt32InBounds A $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
ntp4vc-plength-syn $a class ( NTP4VCPlength A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syn $a wff NTP4VCValid A B $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-is-not-null-syn
  $a wff NTP4VCIsNotNull A B $.
ntp4vc-malloc-shape-syn
  $a wff NTP4VCMallocShape A B C $.
ntp4vc-same-meta-syn
  $a wff NTP4VCSameMeta A B $.
ntp4vc-released-shape-syn
  $a wff NTP4VCReleasedShape A $.
ntp4vc-final-syn
  $a wff NTP4VCFinal A B C D E F $.
ntp4vc-core-pre-syn
  $a wff NTP4VCCorePre A B C D E F G $.
ntp4vc-post-obligation-syn
  $a wff NTP4VCPostObligation A B C D E F G H $.
ntp4vc-after-ny-syn
  $a wff NTP4VCAfterNy A B C D E F G H I $.
ntp4vc-after-nx-syn
  $a wff NTP4VCAfterNx A B C D E F G H $.
ntp4vc-after-o2-syn
  $a wff NTP4VCAfterO2 A B C D E F G H $.
ntp4vc-after-o1-syn
  $a wff NTP4VCAfterO1 A B C D E F G H $.
ntp4vc-vc-syn
  $a wff NTP4VCVC A B C D E F G $.

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

ntp4vc-uint32-in-bounds-def $a
  |- ( NTP4VCUInt32InBounds A <->
      ( A e. ZZ /\
        ( 0 <_ A /\ A < ( 2 ^ ; 3 2 ) ) ) )
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

ntp4vc-is-not-null-def $a
  |- ( NTP4VCIsNotNull A B <->
      ( NTP4VCZone A ) =/= B )
$.

ntp4vc-malloc-shape-def $a
  |- ( NTP4VCMallocShape A B C <->
      ( ( ( ( NTP4VCZone A ) =/= C ->
              ( NTP4VCPlength A ) = B ) /\
          ( NTP4VCOffset A ) = 0 ) /\
        ( ( NTP4VCMin A ) = 0 /\
          ( ( NTP4VCMax A ) = ( NTP4VCPlength A ) /\
            ( NTP4VCWritable A ) = 1 ) ) ) )
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

ntp4vc-released-shape-def $a
  |- ( NTP4VCReleasedShape A <->
      ( ( NTP4VCOffset A ) = 0 /\
        ( ( NTP4VCMin A ) = 0 /\
          ( ( NTP4VCMax A ) = ( NTP4VCPlength A ) /\
            ( NTP4VCWritable A ) = 1 ) ) ) )
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

ntp4vc-core-pre-def $a
  |- ( NTP4VCCorePre A B C D E F G <->
      ( ( ( 1 <_ ( NTP4VCSigned32 A ) /\
            ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B ) ) /\
          ( NTP4VCSigned32 B ) <_
            ( ( ( 2 ^ ; 3 1 ) - 1 ) - 1 ) ) /\
        ( NTP4VCValid C ( NTP4VCSigned32 B ) /\
          ( NTP4VCValid D ( NTP4VCSigned32 A ) /\
            ( NTP4VCValid E
                ( ( ( NTP4VCSigned32 B ) -
                    ( NTP4VCSigned32 A ) ) + 1 ) /\
              ( NTP4VCValid F ( ( NTP4VCSigned32 B ) + 1 ) /\
                ( NTP4VCValid G ( NTP4VCSigned32 A ) /\
                  ( ( ( NTP4VCWritable E ) = 1 /\
                      ( NTP4VCWritable C ) = 1 ) /\
                    ( ( ( NTP4VCWritable F ) = 1 /\
                        ( NTP4VCWritable G ) = 1 ) /\
                      0 < ( NTP4VCPelts D
                        ( ( ( NTP4VCOffset D ) +
                            ( NTP4VCSigned32 A ) ) - 1 ) ) ) ) ) ) ) ) ) ) )
$.

${
  $d n A B C D E F G H $.
  $d m A B C D E F G H $.
  $d x A B C D E F G H $.
  $d q A B C D E F G H $.
  $d n m $.  $d n x $.  $d n q $.
  $d m x $.  $d m q $.  $d x q $.

  ntp4vc-post-obligation-def $a
    |- ( NTP4VCPostObligation A B C D E F G H <->
        A. n e. ( NTP4VCPtr H )
          ( NTP4VCSameMeta n E ->
            A. m e. ( NTP4VCPtr H )
              ( NTP4VCSameMeta m D ->
                A. x e. ( NTP4VCPtr H )
                  ( NTP4VCSameMeta x A ->
                    A. q e. ( NTP4VCPtr H )
                      ( NTP4VCSameMeta q C ->
                        ( NTP4VCFinal A q B x F G ->
                          ( NTP4VCReleasedShape m /\
                            ( NTP4VCReleasedShape n /\
                              NTP4VCFinal A q B x F G ) ) ) ) ) ) ) )
  $.
$}

${
  $d n A B C D E F G H I $.

  ntp4vc-after-ny-def $a
    |- ( NTP4VCAfterNy A B C D E F G H I <->
        A. n e. ( NTP4VCPtr I )
          ( NTP4VCMallocShape n G H ->
            ( ( NTP4VCIsNotNull n H <->
                ( NTP4VCZone n ) =/= H ) ->
              ( NTP4VCIsNotNull n H ->
                ( NTP4VCCorePre F E A B C D n /\
                  NTP4VCPostObligation A B C D n E F I ) ) ) ) )
  $.
$}

${
  $d o A B C D E F G H $.

  ntp4vc-after-nx-def $a
    |- ( NTP4VCAfterNx A B C D E F G H <->
        ( 0 <_ ( NTP4VCSigned32 F ) /\
          A. o e. NTP4VCWord32
            ( o = ( NTP4VCSigned32 F ) ->
              ( 0 <_ o /\
                NTP4VCAfterNy A B C D E F o G H ) ) ) )
  $.
$}

${
  $d n A B C D E F G H $.

  ntp4vc-after-o2-def $a
    |- ( NTP4VCAfterO2 A B C D E F G H <->
        ( 0 <_ F /\
          A. n e. ( NTP4VCPtr H )
            ( NTP4VCMallocShape n F G ->
              ( ( NTP4VCIsNotNull n G <->
                  ( NTP4VCZone n ) =/= G ) ->
                ( NTP4VCIsNotNull n G ->
                  NTP4VCAfterNx A B C n D E G H ) ) ) ) )
  $.
$}

${
  $d o A B C D E F G H $.

  ntp4vc-after-o1-def $a
    |- ( NTP4VCAfterO1 A B C D E F G H <->
        ( NTP4VCUInt32InBounds ( F + 1 ) /\
          A. o e. NTP4VCWord32
            ( o = ( F + 1 ) ->
              NTP4VCAfterO2 A B C D E o G H ) ) )
  $.
$}

${
  $d o A B C D E F G $.

  ntp4vc-vc-def $a
    |- ( NTP4VCVC A B C D E F G <->
        ( 0 <_ ( NTP4VCSigned32 D ) /\
          A. o e. NTP4VCWord32
            ( o = ( NTP4VCSigned32 D ) ->
              NTP4VCAfterO1 A B C D E o F G ) ) )
  $.
$}

${
  $( Source parameters:
     A=sy, B=sx, C=x, D=y, E=q, F=qxn, N=null_zone, Z=zone carrier. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-null-zone-type $e |- N e. Z $.
  ntp4vc-sy-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-x-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- D e. ( NTP4VCPtr Z ) $.
  ntp4vc-q-type $e |- E e. ( NTP4VCPtr Z ) $.
  ntp4vc-qxn-type $e |- F e. NTP4VCWord32 $.
  ntp4vc-fact0 $e
    |- 1 <_ ( NTP4VCSigned32 A )
  $.
  ntp4vc-fact1 $e
    |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B )
  $.
  ntp4vc-fact2 $e
    |- ( NTP4VCSigned32 B ) <_
        ( ( ( 2 ^ ; 3 1 ) - 1 ) - 1 )
  $.
  ntp4vc-fact3 $e
    |- NTP4VCValid C ( NTP4VCSigned32 B )
  $.
  ntp4vc-fact4 $e
    |- NTP4VCValid D ( NTP4VCSigned32 A )
  $.
  ntp4vc-fact5 $e
    |- NTP4VCValid E
        ( ( ( NTP4VCSigned32 B ) -
            ( NTP4VCSigned32 A ) ) + 1 )
  $.
  ntp4vc-fact6 $e
    |- ( NTP4VCWritable C ) = 1
  $.
  ntp4vc-fact7 $e
    |- ( NTP4VCWritable E ) = 1
  $.
  ntp4vc-fact8 $e
    |- ( NTP4VCSigned32 F ) = 0
  $.
  ntp4vc-fact9 $e
    |- 0 < ( NTP4VCPelts D
        ( ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 A ) ) - 1 ) )
  $.

  ntp4vc-pearl-multiprecision-div-wmpn-tdiv-qr-in-place-vc $a
    |- NTP4VCVC C D E B A N Z
  $.
$}
