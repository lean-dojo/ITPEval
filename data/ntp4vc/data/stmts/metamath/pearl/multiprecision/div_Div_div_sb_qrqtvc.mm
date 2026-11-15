$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div_sb_qrqtvc: the verification condition
  for schoolbook multiprecision quotient/remainder division, including
  reciprocal estimation, pointer and limb-array updates, loop invariants,
  quotient correction, and remainder bounds. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source 32- and 64-bit words are their complete canonical integer
  carriers, with exact two's-complement signed interpretation for 32-bit
  words. Pointers retain the finite limb sequence, offset, bounds,
  writability Boolean, and arbitrary zone. Limb lookup is totalized with
  zero outside the finite sequence. ValueSub is the exact little-endian
  radix-2^64 finite sum, and map update is extensional functional update.
  Q1 through Q59 are definitional factorizations of the official generated
  verification condition. The final $a is Metamath's native unproved
  statement encoding; there is no $p declaration.
$)

$c NTP4VCWord32 NTP4VCWord64 NTP4VCDataCarrier NTP4VCPtr
   NTP4VCSigned32 NTP4VCInt32InBounds NTP4VCUint64InBounds NTP4VCToNat
   NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone
   NTP4VCPelts NTP4VCMapBase NTP4VCMapUpdate NTP4VCMapGet
   NTP4VCValueSub NTP4VCValue NTP4VCIPow NTP4VCNthDefault
   NTP4VCValid NTP4VCNormalized NTP4VCReciprocal3By2 NTP4VCCompareInt $.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-data-carrier-syn $a class NTP4VCDataCarrier $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syn $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint64-bounds-syn $a wff ( NTP4VCUint64InBounds A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-map-base-syn $a class ( NTP4VCMapBase A ) $.
ntp4vc-map-update-syn $a class ( NTP4VCMapUpdate A B C ) $.
ntp4vc-map-get-syn $a class ( NTP4VCMapGet A B ) $.
ntp4vc-value-sub-syn $a class ( NTP4VCValueSub A B C ) $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-ipow-syn $a class ( NTP4VCIPow A B ) $.
ntp4vc-nth-default-syn $a class ( NTP4VCNthDefault A B C ) $.
ntp4vc-valid-syn $a wff ( NTP4VCValid A B ) $.
ntp4vc-normalized-syn $a wff ( NTP4VCNormalized A B ) $.
ntp4vc-reciprocal-syn $a wff ( NTP4VCReciprocal3By2 A B C ) $.
ntp4vc-compare-syn $a class ( NTP4VCCompareInt A B ) $.

ntp4vc-word32-def $a |- NTP4VCWord32 = ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.
ntp4vc-word64-def $a |- NTP4VCWord64 = ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.
ntp4vc-data-carrier-def $a |- NTP4VCDataCarrier = ( Word NTP4VCWord64 ) $.
ntp4vc-ptr-def $a |- ( NTP4VCPtr A ) =
  ( NTP4VCDataCarrier X.
    ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) ) ) $.
ntp4vc-signed32-def $a |- ( NTP4VCSigned32 A ) =
  if ( A < ( 2 ^ ; 3 1 ) , A , ( A - ( 2 ^ ; 3 2 ) ) ) $.
ntp4vc-int32-bounds-def $a |- ( NTP4VCInt32InBounds A ) <-> (
  ( A e. ZZ ) /\ ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) ) ) $.
ntp4vc-uint64-bounds-def $a |- ( NTP4VCUint64InBounds A ) <->
  ( A e. NTP4VCWord64 ) $.
ntp4vc-to-nat-def $a |- ( NTP4VCToNat A ) = if ( 0 <_ A , A , 0 ) $.
ntp4vc-data-def $a |- ( NTP4VCData A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 1st ` ( 2nd ` A ) ) $.
ntp4vc-min-def $a |- ( NTP4VCMin A ) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.
ntp4vc-max-def $a |- ( NTP4VCMax A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.
ntp4vc-writable-def $a |- ( NTP4VCWritable A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.
ntp4vc-zone-def $a |- ( NTP4VCZone A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.
ntp4vc-pelts-def $a |- ( NTP4VCPelts A B ) = if ( B < 0 , 0 , if (
  B < ( # ` ( NTP4VCData A ) ) ,
  ( ( NTP4VCData A ) ` B ) , 0 ) ) $.

${
  $d z A $.
  ntp4vc-map-base-def $a |- ( NTP4VCMapBase A ) =
    ( z e. ZZ |-> ( NTP4VCPelts A z ) ) $.
$}
${
  $d z A B C $.
  ntp4vc-map-update-def $a |- ( NTP4VCMapUpdate A B C ) =
    ( z e. ZZ |-> if ( z = B , C , ( A ` z ) ) ) $.
$}
ntp4vc-map-get-def $a |- ( NTP4VCMapGet A B ) = ( A ` B ) $.

${
  $d z A B C $.
  ntp4vc-value-sub-def $a |- ( NTP4VCValueSub A B C ) =
    sum_ z e. ( 0 ..^ ( NTP4VCToNat ( C - B ) ) )
      ( ( NTP4VCMapGet A ( B + z ) ) x. ( ( 2 ^ ; 6 4 ) ^ z ) ) $.
$}
ntp4vc-value-def $a |- ( NTP4VCValue A B ) =
  ( NTP4VCValueSub ( NTP4VCMapBase A ) ( NTP4VCOffset A )
    ( ( NTP4VCOffset A ) + B ) ) $.
ntp4vc-ipow-def $a |- ( NTP4VCIPow A B ) =
  ( A ^ ( NTP4VCToNat B ) ) $.
ntp4vc-nth-default-def $a |- ( NTP4VCNthDefault A B C ) =
  if ( ( NTP4VCToNat B ) < ( # ` A ) ,
       ( A ` ( NTP4VCToNat B ) ) , C ) $.
ntp4vc-valid-def $a |- ( NTP4VCValid A B ) <-> (
  ( NTP4VCInt32InBounds B ) /\
  ( 0 <_ B /\
    ( 0 <_ ( NTP4VCMin A ) /\
      ( ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) /\
        ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
          ( NTP4VCMax A ) <_ ( # ` ( NTP4VCData A ) ) ) ) ) ) ) $.
ntp4vc-normalized-def $a |- ( NTP4VCNormalized A B ) <-> (
  ( NTP4VCValid A ( NTP4VCSigned32 B ) ) /\
  ( ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_
    ( NTP4VCPelts A
      ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) ) - 1 ) ) ) ) $.
ntp4vc-reciprocal-def $a |- ( NTP4VCReciprocal3By2 A B C ) <-> (
  A = ( ( |_ ` (
    ( ( ( ( 2 ^ ; 6 4 ) x. ( 2 ^ ; 6 4 ) ) x. ( 2 ^ ; 6 4 ) ) - 1 )
    / ( C + ( ( 2 ^ ; 6 4 ) x. B ) ) ) ) - ( 2 ^ ; 6 4 ) ) ) $.
ntp4vc-compare-def $a |- ( NTP4VCCompareInt A B ) =
  if ( A < B , ( -u 1 ) , if ( A = B , 0 , 1 ) ) $.

$c NTP4VCQ1 $.
ntp4vc-q1-syn $a wff ( NTP4VCQ1 A B C D ) $.
$c NTP4VCQ2 $.
ntp4vc-q2-syn $a wff ( NTP4VCQ2 A B C ) $.
$c NTP4VCQ3 $.
ntp4vc-q3-syn $a wff ( NTP4VCQ3 A B C D ) $.
$c NTP4VCQ4 $.
ntp4vc-q4-syn $a wff ( NTP4VCQ4 A B C D E F G ) $.
$c NTP4VCQ5 $.
ntp4vc-q5-syn $a wff ( NTP4VCQ5 A B C D E F G H ) $.
$c NTP4VCQ6 $.
ntp4vc-q6-syn $a wff ( NTP4VCQ6 A B ) $.
$c NTP4VCQ7 $.
ntp4vc-q7-syn $a wff ( NTP4VCQ7 A B C ) $.
$c NTP4VCQ8 $.
ntp4vc-q8-syn $a wff ( NTP4VCQ8 A B C D E F G H I J K L M N ) $.
$c NTP4VCQ9 $.
ntp4vc-q9-syn $a wff ( NTP4VCQ9 A B C D E F G H I J K L M N ) $.
$c NTP4VCQ10 $.
ntp4vc-q10-syn $a wff ( NTP4VCQ10 A B C D E F G H I J K L M N O P Q R ) $.
$c NTP4VCQ11 $.
ntp4vc-q11-syn $a wff ( NTP4VCQ11 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ12 $.
ntp4vc-q12-syn $a wff ( NTP4VCQ12 A B C D E F G H I J K L M N O P Q ) $.
$c NTP4VCQ13 $.
ntp4vc-q13-syn $a wff ( NTP4VCQ13 A B ) $.
$c NTP4VCQ14 $.
ntp4vc-q14-syn $a wff ( NTP4VCQ14 A B C ) $.
$c NTP4VCQ15 $.
ntp4vc-q15-syn $a wff ( NTP4VCQ15 A B ) $.
$c NTP4VCQ16 $.
ntp4vc-q16-syn $a wff ( NTP4VCQ16 A B C ) $.
$c NTP4VCQ17 $.
ntp4vc-q17-syn $a wff ( NTP4VCQ17 A B C D E F ) $.
$c NTP4VCQ18 $.
ntp4vc-q18-syn $a wff ( NTP4VCQ18 A B C D E F G ) $.
$c NTP4VCQ19 $.
ntp4vc-q19-syn $a wff ( NTP4VCQ19 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ20 $.
ntp4vc-q20-syn $a wff ( NTP4VCQ20 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ21 $.
ntp4vc-q21-syn $a wff ( NTP4VCQ21 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ22 $.
ntp4vc-q22-syn $a wff ( NTP4VCQ22 A B C D E F G H I J K L M N O P Q R ) $.
$c NTP4VCQ23 $.
ntp4vc-q23-syn $a wff ( NTP4VCQ23 A B C D E F G H I J K L M N O P Q R S T U ) $.
$c NTP4VCQ24 $.
ntp4vc-q24-syn $a wff ( NTP4VCQ24 A B C D E F G H I J K L M N O P Q R S ) $.
$c NTP4VCQ25 $.
ntp4vc-q25-syn $a wff ( NTP4VCQ25 A B C D E F G H I J K L M N O P Q R ) $.
$c NTP4VCQ26 $.
ntp4vc-q26-syn $a wff ( NTP4VCQ26 A B C D E F G H I J K L M N O P Q R S ) $.
$c NTP4VCQ27 $.
ntp4vc-q27-syn $a wff ( NTP4VCQ27 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ28 $.
ntp4vc-q28-syn $a wff ( NTP4VCQ28 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ29 $.
ntp4vc-q29-syn $a wff ( NTP4VCQ29 A B C D E F G H I J K L M N O P Q R S ) $.
$c NTP4VCQ30 $.
ntp4vc-q30-syn $a wff ( NTP4VCQ30 A B C D E F G H I J K L M N O P Q R S T U V ) $.
$c NTP4VCQ31 $.
ntp4vc-q31-syn $a wff ( NTP4VCQ31 A B C D E F G H I J K L M N O P Q R S T U V W ) $.
$c NTP4VCQ32 $.
ntp4vc-q32-syn $a wff ( NTP4VCQ32 A B C D E F G H I J K L M N O P Q R S T U V ) $.
$c NTP4VCQ33 $.
ntp4vc-q33-syn $a wff ( NTP4VCQ33 A B C D E F G H I J K L M N O P Q R S T U V W ) $.
$c NTP4VCQ34 $.
ntp4vc-q34-syn $a wff ( NTP4VCQ34 A B C D E F G H I J K L M N O P Q R S T U V ) $.
$c NTP4VCQ35 $.
ntp4vc-q35-syn $a wff ( NTP4VCQ35 A B C D E F G H I J K L M N O P Q R S T U V W ) $.
$c NTP4VCQ36 $.
ntp4vc-q36-syn $a wff ( NTP4VCQ36 A B C D E F G H I J K L M N O P Q R S T U ) $.
$c NTP4VCQ37 $.
ntp4vc-q37-syn $a wff ( NTP4VCQ37 A B C D E F G H I J K L M N O P Q R S T ) $.
$c NTP4VCQ38 $.
ntp4vc-q38-syn $a wff ( NTP4VCQ38 A B C D E F G H I J K L M N O P Q R S T U ) $.
$c NTP4VCQ39 $.
ntp4vc-q39-syn $a wff ( NTP4VCQ39 A B C D E F G H I J K L M N O P Q R S ) $.
$c NTP4VCQ40 $.
ntp4vc-q40-syn $a wff ( NTP4VCQ40 A B C D E F G H I J K L M N O P Q R S T ) $.
$c NTP4VCQ41 $.
ntp4vc-q41-syn $a wff ( NTP4VCQ41 A B C D E F G H I J K L M N O P Q R S ) $.
$c NTP4VCQ42 $.
ntp4vc-q42-syn $a wff ( NTP4VCQ42 A B C D E F G H I J K L M N O P Q ) $.
$c NTP4VCQ43 $.
ntp4vc-q43-syn $a wff ( NTP4VCQ43 A B C D E F G H I J K L M N O P Q ) $.
$c NTP4VCQ44 $.
ntp4vc-q44-syn $a wff ( NTP4VCQ44 A B C D E F G H I J K L M N O P ) $.
$c NTP4VCQ45 $.
ntp4vc-q45-syn $a wff ( NTP4VCQ45 A B C D E F G H I ) $.
$c NTP4VCQ46 $.
ntp4vc-q46-syn $a wff ( NTP4VCQ46 A B C D E F G H I J K L ) $.
$c NTP4VCQ47 $.
ntp4vc-q47-syn $a wff ( NTP4VCQ47 A B C D E F G H I J K L M N O ) $.
$c NTP4VCQ48 $.
ntp4vc-q48-syn $a wff ( NTP4VCQ48 A B C D E F G H I J K L M N O ) $.
$c NTP4VCQ49 $.
ntp4vc-q49-syn $a wff ( NTP4VCQ49 A B C D E F G H I J K L M N ) $.
$c NTP4VCQ50 $.
ntp4vc-q50-syn $a wff ( NTP4VCQ50 A B C D E F G H I J K L ) $.
$c NTP4VCQ51 $.
ntp4vc-q51-syn $a wff ( NTP4VCQ51 A B C D E F G H I J K ) $.
$c NTP4VCQ52 $.
ntp4vc-q52-syn $a wff ( NTP4VCQ52 A B C D E F G H I J ) $.
$c NTP4VCQ53 $.
ntp4vc-q53-syn $a wff ( NTP4VCQ53 A B C D E F G H I ) $.
$c NTP4VCQ54 $.
ntp4vc-q54-syn $a wff ( NTP4VCQ54 A B C D E F G H ) $.
$c NTP4VCQ55 $.
ntp4vc-q55-syn $a wff ( NTP4VCQ55 A B C D E F G ) $.
$c NTP4VCQ56 $.
ntp4vc-q56-syn $a wff ( NTP4VCQ56 A B C D E F G ) $.
$c NTP4VCQ57 $.
ntp4vc-q57-syn $a wff ( NTP4VCQ57 A B C D E F ) $.
$c NTP4VCQ58 $.
ntp4vc-q58-syn $a wff ( NTP4VCQ58 A B C D E F ) $.
$c NTP4VCQ59 $.
ntp4vc-q59-syn $a wff ( NTP4VCQ59 A B C D E ) $.
${
  $d z e A B C D $.
  ntp4vc-q1-def $a |- ( NTP4VCQ1 A B C D ) <-> A. z ( ( z e. { 0 , 1 } ) -> ( ( ( ( D = 0 ) -> ( z = 1 ) ) /\ ( ( z = 1 ) -> ( D = 0 ) ) ) -> ( -. ( z = 1 ) -> ( ( ( ( 0 <_ ( NTP4VCSigned32 A ) ) /\ ( NTP4VCValid C ( NTP4VCSigned32 A ) ) ) /\ ( NTP4VCValid B ( NTP4VCSigned32 A ) ) ) /\ ( ( NTP4VCWritable C ) = 1 ) ) ) ) ) $.
$}
${
  $d z e A B C $.
  ntp4vc-q2-def $a |- ( NTP4VCQ2 A B C ) <-> A. z ( ( z e. ZZ ) -> ( ( ( z < ( NTP4VCOffset C ) ) \/ ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 A ) ) <_ z ) ) -> ( ( NTP4VCMapGet ( NTP4VCMapBase C ) z ) = ( NTP4VCMapGet ( NTP4VCMapBase B ) z ) ) ) ) $.
$}
${
  $d z x e A B C D $.
  ntp4vc-q3-def $a |- ( NTP4VCQ3 A B C D ) <-> E. z ( ( z e. NTP4VCWord64 ) /\ ( ( ( ( ( NTP4VCValue D ( NTP4VCSigned32 A ) ) - ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. z ) ) = ( ( NTP4VCValue C ( NTP4VCSigned32 A ) ) - ( NTP4VCValue B ( NTP4VCSigned32 A ) ) ) ) /\ ( ( 0 <_ z ) /\ ( z <_ 1 ) ) ) /\ ( NTP4VCQ2 A C D ) ) ) $.
$}
${
  $d z e A B C D E F G $.
  ntp4vc-q4-def $a |- ( NTP4VCQ4 A B C D E F G ) <-> E. z ( ( z e. ( NTP4VCPtr _V ) ) /\ ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData F ) ) /\ ( ( # ` ( NTP4VCData F ) ) = ( # ` ( NTP4VCData E ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset E ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin E ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax E ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable E ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone E ) ) ) /\ ( ( ( ( ( ( ( ( NTP4VCData G ) = ( NTP4VCData F ) ) /\ ( ( # ` ( NTP4VCData F ) ) = ( # ` ( NTP4VCData D ) ) ) ) /\ ( ( NTP4VCOffset G ) = ( NTP4VCOffset D ) ) ) /\ ( ( NTP4VCMin G ) = ( NTP4VCMin D ) ) ) /\ ( ( NTP4VCMax G ) = ( NTP4VCMax D ) ) ) /\ ( ( NTP4VCWritable G ) = ( NTP4VCWritable D ) ) ) /\ ( ( NTP4VCZone G ) = ( NTP4VCZone D ) ) ) ) /\ ( ( # ` ( NTP4VCData F ) ) = ( # ` ( NTP4VCData B ) ) ) ) /\ ( ( NTP4VCOffset F ) = ( NTP4VCOffset B ) ) ) /\ ( ( NTP4VCMin F ) = ( NTP4VCMin B ) ) ) /\ ( ( NTP4VCMax F ) = ( NTP4VCMax B ) ) ) /\ ( ( NTP4VCWritable F ) = ( NTP4VCWritable B ) ) ) /\ ( ( NTP4VCZone F ) = ( NTP4VCZone B ) ) ) /\ ( NTP4VCQ3 A C E z ) ) ) $.
$}
${
  $d z e A B C D E F G H $.
  ntp4vc-q5-def $a |- ( NTP4VCQ5 A B C D E F G H ) <-> E. z ( ( z e. { 0 , 1 } ) /\ ( ( ( ( F = 0 ) -> ( z = 1 ) ) /\ ( ( z = 1 ) -> ( F = 0 ) ) ) /\ ( ( -. ( z = 1 ) -> ( NTP4VCQ4 A B C D E G H ) ) /\ ( -. -. ( z = 1 ) -> ( ( G = B ) /\ ( H = D ) ) ) ) ) ) $.
$}
${
  $d z e A B $.
  ntp4vc-q6-def $a |- ( NTP4VCQ6 A B ) <-> A. z ( ( z e. ZZ ) -> ( ( ( 0 <_ z ) /\ ( z < ( # ` B ) ) ) -> ( ( NTP4VCNthDefault B ( NTP4VCToNat z ) 0 ) = ( NTP4VCNthDefault A ( NTP4VCToNat z ) 0 ) ) ) ) $.
$}
${
  $d z e A B C $.
  ntp4vc-q7-def $a |- ( NTP4VCQ7 A B C ) <-> A. z ( ( z e. ZZ ) -> ( ( ( z < ( NTP4VCOffset C ) ) \/ ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 A ) ) <_ z ) ) -> ( ( NTP4VCMapGet ( NTP4VCMapBase C ) z ) = ( NTP4VCMapGet ( NTP4VCMapBase B ) z ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N $.
  ntp4vc-q8-def $a |- ( NTP4VCQ8 A B C D E F G H I J K L M N ) <-> A. z A. y ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( y e. ( NTP4VCPtr _V ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData N ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset N ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin N ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax N ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable N ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone N ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData N ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset N ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin N ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax N ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable N ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone N ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData J ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset J ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable J ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone J ) ) ) -> ( ( ( NTP4VCMapBase z ) = ( NTP4VCMapUpdate ( NTP4VCMapBase N ) ( NTP4VCOffset z ) ( ( 2 ^ ; 6 4 ) - 1 ) ) ) -> ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( NTP4VCSigned32 K ) < ( NTP4VCSigned32 I ) ) /\ ( ( 0 <_ ( NTP4VCSigned32 K ) ) /\ ( ( NTP4VCSigned32 K ) <_ ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset y ) + ( NTP4VCSigned32 K ) ) ) ) /\ ( ( NTP4VCOffset L ) = ( ( ( ( NTP4VCOffset M ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 2 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData y ) ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin y ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax y ) ) ) /\ ( ( # ` ( NTP4VCData L ) ) = ( # ` ( NTP4VCData M ) ) ) ) /\ ( ( NTP4VCMin L ) = ( NTP4VCMin M ) ) ) /\ ( ( NTP4VCMax L ) = ( NTP4VCMax M ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase y ) ) ) /\ ( ( NTP4VCMapBase L ) = ( NTP4VCMapBase M ) ) ) /\ ( ( ( NTP4VCWritable z ) = 1 ) /\ ( ( NTP4VCWritable L ) = 1 ) ) ) /\ ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( ( ( NTP4VCValue z ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) + ( H x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) ) ) x. G ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 K ) ) ) + ( NTP4VCValue M ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) x. ( NTP4VCMapGet ( NTP4VCMapBase L ) ( ( NTP4VCOffset L ) + 1 ) ) ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase M ) ( ( NTP4VCOffset L ) + ( NTP4VCSigned32 F ) ) ( ( ( ( NTP4VCOffset L ) + ( NTP4VCSigned32 F ) ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. ( NTP4VCMapGet ( NTP4VCMapBase L ) ( ( NTP4VCOffset L ) + 1 ) ) ) ) < G ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase M ) ( NTP4VCOffset L ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. ( NTP4VCMapGet ( NTP4VCMapBase L ) ( ( NTP4VCOffset L ) + 1 ) ) ) ) <_ ( E + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. D ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N $.
  ntp4vc-q9-def $a |- ( NTP4VCQ9 A B C D E F G H I J K L M N ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset J ) + ( -u 1 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData J ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase J ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData J ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone J ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable J ) ) ) -> ( ( ( ( ( NTP4VCOffset z ) + 1 ) <_ ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) /\ ( ( ( NTP4VCOffset z ) < ( ( NTP4VCOffset z ) + 1 ) ) \/ ( ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) <_ ( NTP4VCOffset z ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase K ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase K ) ( NTP4VCOffset z ) ( ( 2 ^ ; 6 4 ) - 1 ) ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) ) -> ( ( ( ( ( NTP4VCMin z ) <_ ( NTP4VCOffset z ) ) /\ ( ( NTP4VCOffset z ) < ( NTP4VCMax z ) ) ) /\ ( ( NTP4VCWritable z ) = 1 ) ) /\ ( NTP4VCQ8 A B C D E F G H I K L M N z ) ) ) ) ) ) $.
$}
${
  $d z x u e A B C D E F G H I J K L M N O P Q R $.
  ntp4vc-q10-def $a |- ( NTP4VCQ10 A B C D E F G H I J K L M N O P Q R ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( ( NTP4VCValue P ( NTP4VCSigned32 A ) ) - ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. z ) ) = ( ( NTP4VCValue O ( NTP4VCSigned32 A ) ) - ( ( NTP4VCValue D ( NTP4VCSigned32 A ) ) x. ( ( 2 ^ ; 6 4 ) - 1 ) ) ) ) /\ ( NTP4VCQ7 A O P ) ) -> ( ( ( NTP4VCValue R ( NTP4VCSigned32 N ) ) = ( NTP4VCValue L ( NTP4VCSigned32 N ) ) ) /\ ( ( ( NTP4VCValue R ( NTP4VCSigned32 N ) ) = ( NTP4VCValue L ( NTP4VCSigned32 N ) ) ) -> ( ( ( ( NTP4VCOffset R ) <_ ( NTP4VCOffset P ) ) /\ ( ( NTP4VCOffset P ) <_ ( ( NTP4VCOffset R ) + ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 N ) ) - 1 ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase R ) ( NTP4VCOffset R ) ( ( NTP4VCOffset R ) + ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 N ) ) - 1 ) ) ) = ( ( NTP4VCValueSub ( NTP4VCMapBase R ) ( NTP4VCOffset R ) ( NTP4VCOffset P ) ) + ( ( NTP4VCValueSub ( NTP4VCMapBase R ) ( NTP4VCOffset P ) ( ( NTP4VCOffset R ) + ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 N ) ) - 1 ) ) ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCOffset P ) - ( NTP4VCOffset R ) ) ) ) ) ) -> ( ( ( ( ( NTP4VCMin Q ) <_ ( ( NTP4VCOffset Q ) + 1 ) ) /\ ( ( ( NTP4VCOffset Q ) + 1 ) < ( NTP4VCMax Q ) ) ) /\ ( ( ( NTP4VCMin K ) <_ ( ( NTP4VCOffset K ) + ( -u 1 ) ) ) /\ ( ( ( NTP4VCOffset K ) + ( -u 1 ) ) <_ ( NTP4VCMax K ) ) ) ) /\ ( NTP4VCQ9 A B C E F G H I J K M N Q R ) ) ) ) ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P $.
  ntp4vc-q11-def $a |- ( NTP4VCQ11 A B C D E F G H I J K L M N O P ) <-> A. z A. y A. x ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( ( y e. ( NTP4VCPtr _V ) ) /\ ( x e. ( NTP4VCPtr _V ) ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData y ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData O ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset O ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin O ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax O ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable O ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone O ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData L ) ) ) /\ ( ( NTP4VCOffset x ) = ( NTP4VCOffset L ) ) ) /\ ( ( NTP4VCMin x ) = ( NTP4VCMin L ) ) ) /\ ( ( NTP4VCMax x ) = ( NTP4VCMax L ) ) ) /\ ( ( NTP4VCWritable x ) = ( NTP4VCWritable L ) ) ) /\ ( ( NTP4VCZone x ) = ( NTP4VCZone L ) ) ) -> ( NTP4VCQ10 A B C D E F G H I J K L M N P z y x ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q $.
  ntp4vc-q12-def $a |- ( NTP4VCQ12 A B C D E F G H I J K L M N O P Q ) <-> A. z ( ( z e. NTP4VCDataCarrier ) -> ( ( ( ( # ` z ) = ( # ` Q ) ) /\ ( NTP4VCQ6 Q z ) ) -> ( ( ( ( NTP4VCValid D ( NTP4VCSigned32 A ) ) /\ ( NTP4VCValid P ( NTP4VCSigned32 A ) ) ) /\ ( ( NTP4VCWritable P ) = 1 ) ) /\ ( NTP4VCQ11 A B C D E F G H I J K L M N O P ) ) ) ) $.
$}
${
  $d z e A B $.
  ntp4vc-q13-def $a |- ( NTP4VCQ13 A B ) <-> A. z ( ( z e. ZZ ) -> ( ( ( 0 <_ z ) /\ ( z < ( # ` B ) ) ) -> ( ( NTP4VCNthDefault B ( NTP4VCToNat z ) 0 ) = ( NTP4VCNthDefault A ( NTP4VCToNat z ) 0 ) ) ) ) $.
$}
${
  $d z e A B C $.
  ntp4vc-q14-def $a |- ( NTP4VCQ14 A B C ) <-> A. z ( ( z e. ZZ ) -> ( ( ( z < ( NTP4VCOffset C ) ) \/ ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) ) <_ z ) ) -> ( ( NTP4VCMapGet ( NTP4VCMapBase C ) z ) = ( NTP4VCMapGet ( NTP4VCMapBase A ) z ) ) ) ) $.
$}
${
  $d z e A B $.
  ntp4vc-q15-def $a |- ( NTP4VCQ15 A B ) <-> A. z ( ( z e. ZZ ) -> ( ( ( 0 <_ z ) /\ ( z < ( # ` B ) ) ) -> ( ( NTP4VCNthDefault B ( NTP4VCToNat z ) 0 ) = ( NTP4VCNthDefault A ( NTP4VCToNat z ) 0 ) ) ) ) $.
$}
${
  $d z e A B C $.
  ntp4vc-q16-def $a |- ( NTP4VCQ16 A B C ) <-> A. z ( ( z e. ZZ ) -> ( ( ( z < ( NTP4VCOffset C ) ) \/ ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) ) <_ z ) ) -> ( ( NTP4VCMapGet ( NTP4VCMapBase C ) z ) = ( NTP4VCMapGet ( NTP4VCMapBase A ) z ) ) ) ) $.
$}
${
  $d z x e A B C D E F $.
  ntp4vc-q17-def $a |- ( NTP4VCQ17 A B C D E F ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( z = ( ( C + F ) mod ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ) ) -> ( ( ( NTP4VCValue E ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. z ) ) = ( ( ( ( NTP4VCValue D ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. C ) ) + B ) - ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G $.
  ntp4vc-q18-def $a |- ( NTP4VCQ18 A B C D E F G ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( z = ( ( B + G ) mod ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ) ) -> ( NTP4VCQ17 A C D E F z ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P $.
  ntp4vc-q19-def $a |- ( NTP4VCQ19 A B C D E F G H I J K L M N O P ) <-> A. z A. y ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( y e. ( NTP4VCPtr _V ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData J ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset J ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable J ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone J ) ) ) -> ( ( ( NTP4VCMapBase z ) = ( NTP4VCMapUpdate ( NTP4VCMapBase P ) ( NTP4VCOffset z ) O ) ) -> ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( NTP4VCSigned32 K ) < ( NTP4VCSigned32 I ) ) /\ ( ( 0 <_ ( NTP4VCSigned32 K ) ) /\ ( ( NTP4VCSigned32 K ) <_ ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset y ) + ( NTP4VCSigned32 K ) ) ) ) /\ ( ( NTP4VCOffset L ) = ( ( ( ( NTP4VCOffset M ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 2 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData y ) ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin y ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax y ) ) ) /\ ( ( # ` ( NTP4VCData L ) ) = ( # ` ( NTP4VCData M ) ) ) ) /\ ( ( NTP4VCMin L ) = ( NTP4VCMin M ) ) ) /\ ( ( NTP4VCMax L ) = ( NTP4VCMax M ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase y ) ) ) /\ ( ( NTP4VCMapBase L ) = ( NTP4VCMapBase M ) ) ) /\ ( ( ( NTP4VCWritable z ) = 1 ) /\ ( ( NTP4VCWritable L ) = 1 ) ) ) /\ ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( ( ( NTP4VCValue z ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) + ( H x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) ) ) x. G ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 K ) ) ) + ( NTP4VCValue M ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) x. N ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase M ) ( ( NTP4VCOffset L ) + ( NTP4VCSigned32 F ) ) ( ( ( ( NTP4VCOffset L ) + ( NTP4VCSigned32 F ) ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. N ) ) < G ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase M ) ( NTP4VCOffset L ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. N ) ) <_ ( E + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. D ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N O P $.
  ntp4vc-q20-def $a |- ( NTP4VCQ20 A B C D E F G H I J K L M N O P ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset J ) + ( -u 1 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData J ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase J ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData J ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone J ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable J ) ) ) -> ( ( ( ( ( NTP4VCOffset z ) + 1 ) <_ ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) /\ ( ( ( NTP4VCOffset z ) < ( ( NTP4VCOffset z ) + 1 ) ) \/ ( ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) <_ ( NTP4VCOffset z ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase K ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase K ) ( NTP4VCOffset z ) P ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) ) -> ( ( ( ( ( NTP4VCMin z ) <_ ( NTP4VCOffset z ) ) /\ ( ( NTP4VCOffset z ) < ( NTP4VCMax z ) ) ) /\ ( ( NTP4VCWritable z ) = 1 ) ) /\ ( NTP4VCQ19 A B C D E F G H I K L M N O P z ) ) ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N O P $.
  ntp4vc-q21-def $a |- ( NTP4VCQ21 A B C D E F G H I J K L M N O P ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( z = ( M - 1 ) ) -> ( ( ( ( NTP4VCMin J ) <_ ( ( NTP4VCOffset J ) + ( -u 1 ) ) ) /\ ( ( ( NTP4VCOffset J ) + ( -u 1 ) ) <_ ( NTP4VCMax J ) ) ) /\ ( NTP4VCQ20 A B C D E F G H I J K L N O P z ) ) ) ) $.
$}
${
  $d z x e A B C D E F G H I J K L M N O P Q R $.
  ntp4vc-q22-def $a |- ( NTP4VCQ22 A B C D E F G H I J K L M N O P Q R ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( NTP4VCValue P ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. z ) ) = ( ( ( ( NTP4VCValue O ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. N ) ) + G ) - ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) ) ) -> ( ( NTP4VCUint64InBounds ( M - 1 ) ) /\ ( NTP4VCQ21 A B C D E F G H I J K L M Q R z ) ) ) ) $.
$}
${
  $d z x e A B C D E F G H I J K L M N O P Q R S T U $.
  ntp4vc-q23-def $a |- ( NTP4VCQ23 A B C D E F G H I J K L M N O P Q R S T U ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( ( 0 <_ z ) /\ ( z <_ 1 ) ) /\ ( ( ( NTP4VCValue S ( NTP4VCSigned32 R ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 R ) ) x. z ) ) = ( ( NTP4VCValue P ( NTP4VCSigned32 R ) ) + ( NTP4VCValue D ( NTP4VCSigned32 R ) ) ) ) ) /\ ( NTP4VCQ16 P R S ) ) -> ( ( ( NTP4VCValue U ( NTP4VCSigned32 M ) ) = ( NTP4VCValue Q ( NTP4VCSigned32 M ) ) ) /\ ( ( ( NTP4VCValue U ( NTP4VCSigned32 M ) ) = ( NTP4VCValue Q ( NTP4VCSigned32 M ) ) ) -> ( ( -. ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) = 0 ) /\ ( NTP4VCQ18 A E H O P S z ) ) /\ ( NTP4VCQ22 A B C E F G H I J K L M N O P S T U ) ) ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P Q R S $.
  ntp4vc-q24-def $a |- ( NTP4VCQ24 A B C D E F G H I J K L M N O P Q R S ) <-> A. z A. y A. x ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( ( y e. ( NTP4VCPtr _V ) ) /\ ( x e. ( NTP4VCPtr _V ) ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData y ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData Q ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset Q ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin Q ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax Q ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable Q ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone Q ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData R ) ) ) /\ ( ( NTP4VCOffset x ) = ( NTP4VCOffset R ) ) ) /\ ( ( NTP4VCMin x ) = ( NTP4VCMin R ) ) ) /\ ( ( NTP4VCMax x ) = ( NTP4VCMax R ) ) ) /\ ( ( NTP4VCWritable x ) = ( NTP4VCWritable R ) ) ) /\ ( ( NTP4VCZone x ) = ( NTP4VCZone R ) ) ) -> ( NTP4VCQ23 A B C D E F G H I J K L M N O P R S z y x ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R $.
  ntp4vc-q25-def $a |- ( NTP4VCQ25 A B C D E F G H I J K L M N O P Q R ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 A ) - 1 ) ) -> ( ( ( ( NTP4VCValid P ( NTP4VCSigned32 z ) ) /\ ( NTP4VCValid D ( NTP4VCSigned32 z ) ) ) /\ ( ( NTP4VCWritable P ) = 1 ) ) /\ ( NTP4VCQ24 A B C D E F G H I J K L M N O P Q R z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S $.
  ntp4vc-q26-def $a |- ( NTP4VCQ26 A B C D E F G H I J K L M N O P Q R S ) <-> A. z ( ( z e. NTP4VCDataCarrier ) -> ( ( ( ( # ` z ) = ( # ` S ) ) /\ ( NTP4VCQ15 S z ) ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 A ) - 1 ) ) /\ ( NTP4VCQ25 A B C D E F G H I J K L M N O P Q R ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P $.
  ntp4vc-q27-def $a |- ( NTP4VCQ27 A B C D E F G H I J K L M N O P ) <-> A. z A. y ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( y e. ( NTP4VCPtr _V ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData J ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset J ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable J ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone J ) ) ) -> ( ( ( NTP4VCMapBase z ) = ( NTP4VCMapUpdate ( NTP4VCMapBase P ) ( NTP4VCOffset z ) L ) ) -> ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( NTP4VCSigned32 K ) < ( NTP4VCSigned32 I ) ) /\ ( ( 0 <_ ( NTP4VCSigned32 K ) ) /\ ( ( NTP4VCSigned32 K ) <_ ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset y ) + ( NTP4VCSigned32 K ) ) ) ) /\ ( ( NTP4VCOffset N ) = ( ( ( ( NTP4VCOffset O ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 2 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData y ) ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin y ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax y ) ) ) /\ ( ( # ` ( NTP4VCData N ) ) = ( # ` ( NTP4VCData O ) ) ) ) /\ ( ( NTP4VCMin N ) = ( NTP4VCMin O ) ) ) /\ ( ( NTP4VCMax N ) = ( NTP4VCMax O ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase y ) ) ) /\ ( ( NTP4VCMapBase N ) = ( NTP4VCMapBase O ) ) ) /\ ( ( ( NTP4VCWritable z ) = 1 ) /\ ( ( NTP4VCWritable N ) = 1 ) ) ) /\ ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( ( ( NTP4VCValue z ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) + ( H x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) ) ) x. G ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 K ) ) ) + ( NTP4VCValue O ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) x. M ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase O ) ( ( NTP4VCOffset N ) + ( NTP4VCSigned32 F ) ) ( ( ( ( NTP4VCOffset N ) + ( NTP4VCSigned32 F ) ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. M ) ) < G ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase O ) ( NTP4VCOffset N ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. M ) ) <_ ( E + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. D ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N O P $.
  ntp4vc-q28-def $a |- ( NTP4VCQ28 A B C D E F G H I J K L M N O P ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset J ) + ( -u 1 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData J ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase J ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData J ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin J ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax J ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone J ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable J ) ) ) -> ( ( ( ( ( NTP4VCOffset z ) + 1 ) <_ ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) /\ ( ( ( NTP4VCOffset z ) < ( ( NTP4VCOffset z ) + 1 ) ) \/ ( ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) <_ ( NTP4VCOffset z ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase K ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase K ) ( NTP4VCOffset z ) M ) ( ( NTP4VCOffset z ) + 1 ) ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 B ) ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 L ) ) ) ) -> ( ( ( ( ( NTP4VCMin z ) <_ ( NTP4VCOffset z ) ) /\ ( ( NTP4VCOffset z ) < ( NTP4VCMax z ) ) ) /\ ( ( NTP4VCWritable z ) = 1 ) ) /\ ( NTP4VCQ27 A B C D E F G H I K L M N O P z ) ) ) ) ) ) $.
$}
${
  $d z x u e A B C D E F G H I J K L M N O P Q R S $.
  ntp4vc-q29-def $a |- ( NTP4VCQ29 A B C D E F G H I J K L M N O P Q R S ) <-> A. z ( ( z e. { 0 , 1 } ) -> ( ( ( ( O = 0 ) -> ( z = 1 ) ) /\ ( ( z = 1 ) -> ( O = 0 ) ) ) -> ( ( -. ( z = 1 ) -> ( ( 0 < N ) /\ ( ( 0 < N ) -> ( ( ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) - H ) <_ ( ( NTP4VCValue Q ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. P ) ) ) /\ ( ( ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) - H ) <_ ( ( NTP4VCValue Q ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. P ) ) ) -> ( NTP4VCQ26 A B C D E F G H I J K L M N P Q R S ( NTP4VCData S ) ) ) ) ) ) ) /\ ( -. -. ( z = 1 ) -> ( ( ( ( NTP4VCMin K ) <_ ( ( NTP4VCOffset K ) + ( -u 1 ) ) ) /\ ( ( ( NTP4VCOffset K ) + ( -u 1 ) ) <_ ( NTP4VCMax K ) ) ) /\ ( NTP4VCQ28 A B C E F G H I J K L M N P R S ) ) ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P Q R S T U V $.
  ntp4vc-q30-def $a |- ( NTP4VCQ30 A B C D E F G H I J K L M N O P Q R S T U V ) <-> A. z A. y A. x ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( ( y e. ( NTP4VCPtr _V ) ) /\ ( x e. ( NTP4VCPtr _V ) ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData y ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData R ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset R ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin R ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax R ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable R ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone R ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData Q ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset Q ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin Q ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax Q ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable Q ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone Q ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData y ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData R ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset R ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin R ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax R ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable R ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone R ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData S ) ) ) /\ ( ( NTP4VCOffset x ) = ( NTP4VCOffset S ) ) ) /\ ( ( NTP4VCMin x ) = ( NTP4VCMin S ) ) ) /\ ( ( NTP4VCMax x ) = ( NTP4VCMax S ) ) ) /\ ( ( NTP4VCWritable x ) = ( NTP4VCWritable S ) ) ) /\ ( ( NTP4VCZone x ) = ( NTP4VCZone S ) ) ) -> ( ( ( NTP4VCMapBase y ) = ( NTP4VCMapUpdate ( NTP4VCMapBase R ) ( NTP4VCOffset y ) T ) ) -> ( ( ( ( ( NTP4VCValue z ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. V ) ) - ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. U ) ) = ( ( ( NTP4VCValue O ( NTP4VCSigned32 A ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. J ) ) - ( P x. H ) ) ) /\ ( ( ( ( ( NTP4VCValue z ( ( NTP4VCSigned32 A ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. V ) ) - ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. U ) ) = ( ( ( NTP4VCValue O ( NTP4VCSigned32 A ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 A ) ) x. J ) ) - ( P x. H ) ) ) -> ( NTP4VCQ29 A B C D E F G H I K L M N P U V z y x ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z x e A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-q31-def $a |- ( NTP4VCQ31 A B C D E F G H I J K L M N O P Q R S T U V W ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( z = ( ( Q - U ) mod ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ) ) -> ( ( ( ( NTP4VCOffset R ) <_ ( NTP4VCOffset S ) ) /\ ( ( NTP4VCOffset S ) < ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 1 ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase T ) ( NTP4VCOffset S ) V ) ( NTP4VCOffset R ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 1 ) ) = ( ( NTP4VCValueSub ( NTP4VCMapBase T ) ( NTP4VCOffset R ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCOffset S ) - ( NTP4VCOffset R ) ) ) x. ( V - ( NTP4VCMapGet ( NTP4VCMapBase T ) ( NTP4VCOffset S ) ) ) ) ) ) -> ( ( ( ( NTP4VCOffset T ) <_ ( ( NTP4VCOffset T ) + ( NTP4VCSigned32 N ) ) ) /\ ( ( ( NTP4VCOffset S ) < ( NTP4VCOffset T ) ) \/ ( ( ( NTP4VCOffset T ) + ( NTP4VCSigned32 N ) ) <_ ( NTP4VCOffset S ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase T ) ( NTP4VCOffset T ) ( ( NTP4VCOffset T ) + ( NTP4VCSigned32 N ) ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase T ) ( NTP4VCOffset S ) V ) ( NTP4VCOffset T ) ( ( NTP4VCOffset T ) + ( NTP4VCSigned32 N ) ) ) ) -> ( ( ( ( NTP4VCOffset R ) <_ ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 2 ) ) /\ ( ( ( NTP4VCOffset S ) < ( NTP4VCOffset R ) ) \/ ( ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 2 ) <_ ( NTP4VCOffset S ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase T ) ( NTP4VCOffset R ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 2 ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase T ) ( NTP4VCOffset S ) V ) ( NTP4VCOffset R ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 2 ) ) ) -> ( ( ( ( ( NTP4VCMin S ) <_ ( NTP4VCOffset S ) ) /\ ( ( NTP4VCOffset S ) < ( NTP4VCMax S ) ) ) /\ ( ( NTP4VCWritable S ) = 1 ) ) /\ ( NTP4VCQ30 A B C D E F G H I J K L M N O P R S T V W z ) ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S T U V $.
  ntp4vc-q32-def $a |- ( NTP4VCQ32 A B C D E F G H I J K L M N O P Q R S T U V ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( Q < U ) -> ( z = 1 ) ) /\ ( -. ( Q < U ) -> ( z = 0 ) ) ) -> ( NTP4VCQ31 A B C D E F G H I J K L M N O P Q R S T U V z ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-q33-def $a |- ( NTP4VCQ33 A B C D E F G H I J K L M N O P Q R S T U V W ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( z = ( ( Q - V ) mod ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ) ) -> ( NTP4VCQ32 A B C D E F G H I J K L M N O P R S T U W z ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S T U V $.
  ntp4vc-q34-def $a |- ( NTP4VCQ34 A B C D E F G H I J K L M N O P Q R S T U V ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( Q < V ) -> ( z = 1 ) ) /\ ( -. ( Q < V ) -> ( z = 0 ) ) ) -> ( NTP4VCQ33 A B C D E F G H I J K L M N O P Q R S T U V z ) ) ) $.
$}
${
  $d z x e A B C D E F G H I J K L M N O P Q R S T U V W $.
  ntp4vc-q35-def $a |- ( NTP4VCQ35 A B C D E F G H I J K L M N O P Q R S T U V W ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( ( NTP4VCValue U ( NTP4VCSigned32 T ) ) - ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 T ) ) x. z ) ) = ( ( NTP4VCValue P ( NTP4VCSigned32 T ) ) - ( ( NTP4VCValue D ( NTP4VCSigned32 T ) ) x. Q ) ) ) /\ ( NTP4VCQ14 P T U ) ) -> ( ( ( NTP4VCValue W ( NTP4VCSigned32 O ) ) = ( NTP4VCValue M ( NTP4VCSigned32 O ) ) ) /\ ( ( ( NTP4VCValue W ( NTP4VCSigned32 O ) ) = ( NTP4VCValue M ( NTP4VCSigned32 O ) ) ) -> ( NTP4VCQ34 A B C D E F G H I J K L N O P Q R S U V W z ) ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P Q R S T U $.
  ntp4vc-q36-def $a |- ( NTP4VCQ36 A B C D E F G H I J K L M N O P Q R S T U ) <-> A. z A. y A. x ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( ( y e. ( NTP4VCPtr _V ) ) /\ ( x e. ( NTP4VCPtr _V ) ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData Q ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset Q ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin Q ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax Q ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable Q ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone Q ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData y ) = ( NTP4VCData x ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData P ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset P ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin P ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax P ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable P ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone P ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData M ) ) ) /\ ( ( NTP4VCOffset x ) = ( NTP4VCOffset M ) ) ) /\ ( ( NTP4VCMin x ) = ( NTP4VCMin M ) ) ) /\ ( ( NTP4VCMax x ) = ( NTP4VCMax M ) ) ) /\ ( ( NTP4VCWritable x ) = ( NTP4VCWritable M ) ) ) /\ ( ( NTP4VCZone x ) = ( NTP4VCZone M ) ) ) -> ( NTP4VCQ35 A B C D E F G H I J K L M N O Q R S T U z y x ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S T $.
  ntp4vc-q37-def $a |- ( NTP4VCQ37 A B C D E F G H I J K L M N O P Q R S T ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 A ) - 2 ) ) -> ( ( ( ( NTP4VCValid D ( NTP4VCSigned32 z ) ) /\ ( NTP4VCValid Q ( NTP4VCSigned32 z ) ) ) /\ ( ( NTP4VCWritable Q ) = 1 ) ) /\ ( NTP4VCQ36 A B C D E F G H I J K L M N O P Q R S T z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S T U $.
  ntp4vc-q38-def $a |- ( NTP4VCQ38 A B C D E F G H I J K L M N O P Q R S T U ) <-> A. z ( ( z e. NTP4VCDataCarrier ) -> ( ( ( ( # ` z ) = ( # ` U ) ) /\ ( NTP4VCQ13 U z ) ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 A ) - 2 ) ) /\ ( NTP4VCQ37 A B C D E F G H I J K L M N O P Q R S T ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O P Q R S $.
  ntp4vc-q39-def $a |- ( NTP4VCQ39 A B C D E F G H I J K L M N O P Q R S ) <-> A. z A. y A. x ( ( ( z e. NTP4VCWord64 ) /\ ( ( y e. NTP4VCWord64 ) /\ ( x e. NTP4VCWord64 ) ) ) -> ( ( ( ( ( ( ( ( z x. F ) + ( ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. z ) x. E ) ) + y ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. x ) ) = ( ( R + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. S ) ) + ( ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ) x. J ) ) ) /\ ( 0 <_ ( y + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. x ) ) ) ) /\ ( ( y + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. x ) ) < ( F + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. E ) ) ) ) -> ( ( ( ( NTP4VCOffset M ) <_ ( NTP4VCOffset Q ) ) /\ ( ( NTP4VCOffset Q ) <_ ( ( ( ( NTP4VCOffset M ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 1 ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase M ) ( NTP4VCOffset M ) ( ( ( ( NTP4VCOffset M ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 1 ) ) = ( ( NTP4VCValueSub ( NTP4VCMapBase M ) ( NTP4VCOffset M ) ( NTP4VCOffset Q ) ) + ( ( NTP4VCValueSub ( NTP4VCMapBase M ) ( NTP4VCOffset Q ) ( ( ( ( NTP4VCOffset M ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 1 ) ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCOffset Q ) - ( NTP4VCOffset M ) ) ) ) ) ) -> ( NTP4VCQ38 A B C D E F G H I J K L M N O P Q z y x ( NTP4VCData M ) ) ) ) ) ) $.
$}
${
  $d z x e A B C D E F G H I J K L M N O P Q R S T $.
  ntp4vc-q40-def $a |- ( NTP4VCQ40 A B C D E F G H I J K L M N O P Q R S T ) <-> A. z ( ( z e. { 0 , 1 } ) -> ( ( ( ( T = 1 ) -> ( ( ( S = F ) -> ( z = 1 ) ) /\ ( ( z = 1 ) -> ( S = F ) ) ) ) /\ ( -. ( T = 1 ) -> ( z = 0 ) ) ) -> ( ( ( z = 1 ) -> ( ( ( ( ( NTP4VCValueSub ( NTP4VCMapBase R ) ( ( NTP4VCOffset R ) + 1 ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 2 ) ) x. F ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. E ) ) < I ) /\ ( ( ( ( ( NTP4VCValueSub ( NTP4VCMapBase R ) ( ( NTP4VCOffset R ) + 1 ) ( ( ( NTP4VCOffset R ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 2 ) ) x. F ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. E ) ) < I ) -> ( NTP4VCQ12 A B C D E F H I J L M N O P Q R ( NTP4VCData N ) ) ) ) ) /\ ( -. ( z = 1 ) -> ( ( ( ( NTP4VCMin Q ) <_ ( NTP4VCOffset Q ) ) /\ ( ( NTP4VCOffset Q ) < ( NTP4VCMax Q ) ) ) /\ ( ( ( ( NTP4VCMin Q ) <_ ( ( NTP4VCOffset Q ) + 1 ) ) /\ ( ( ( NTP4VCOffset Q ) + 1 ) < ( NTP4VCMax Q ) ) ) /\ ( ( ( NTP4VCValue R ( NTP4VCSigned32 A ) ) = ( ( NTP4VCValue R ( ( NTP4VCSigned32 A ) - 2 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 2 ) ) x. ( ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( NTP4VCOffset Q ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( ( NTP4VCOffset Q ) + 1 ) ) ) ) ) ) ) /\ ( ( ( NTP4VCValue R ( NTP4VCSigned32 A ) ) = ( ( NTP4VCValue R ( ( NTP4VCSigned32 A ) - 2 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 2 ) ) x. ( ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( NTP4VCOffset Q ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( ( NTP4VCOffset Q ) + 1 ) ) ) ) ) ) ) -> ( ( ( ( ( |_ ` ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) / 2 ) ) <_ E ) /\ ( NTP4VCReciprocal3By2 G E F ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( ( NTP4VCOffset Q ) + 1 ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. K ) ) < ( F + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. E ) ) ) ) /\ ( NTP4VCQ39 A B C D E F H I J K L M N O P Q R ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( NTP4VCOffset Q ) ) ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( ( NTP4VCOffset Q ) + 1 ) ) ) ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q R S $.
  ntp4vc-q41-def $a |- ( NTP4VCQ41 A B C D E F G H I J K L M N O P Q R S ) <-> A. z ( ( z e. { 0 , 1 } ) -> ( ( ( ( K = E ) -> ( z = 1 ) ) /\ ( ( z = 1 ) -> ( K = E ) ) ) -> ( NTP4VCQ40 A B C D E F G H I J K L M N O P Q R S z ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O P Q $.
  ntp4vc-q42-def $a |- ( NTP4VCQ42 A B C D E F G H I J K L M N O P Q ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset Q ) + ( NTP4VCSigned32 H ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData Q ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase Q ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData Q ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin Q ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax Q ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone Q ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable Q ) ) ) -> ( ( ( ( NTP4VCMin Q ) <_ ( ( NTP4VCOffset Q ) + 1 ) ) /\ ( ( ( NTP4VCOffset Q ) + 1 ) < ( NTP4VCMax Q ) ) ) /\ ( NTP4VCQ41 A B C D E F G H I J K L M N O P Q z ( NTP4VCMapGet ( NTP4VCMapBase Q ) ( ( NTP4VCOffset Q ) + 1 ) ) ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N O P Q $.
  ntp4vc-q43-def $a |- ( NTP4VCQ43 A B C D E F G H I J K L M N O P Q ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset N ) + ( -u 1 ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData N ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase N ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData N ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin N ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax N ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone N ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable N ) ) ) -> ( ( ( ( NTP4VCMin z ) <_ ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 H ) ) ) /\ ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 H ) ) <_ ( NTP4VCMax z ) ) ) /\ ( NTP4VCQ42 A B C D E F G H I J K L M O P Q z ) ) ) ) $.
$}
${
  $d z u e A B C D E F G H I J K L M N O P $.
  ntp4vc-q44-def $a |- ( NTP4VCQ44 A B C D E F G H I J K L M N O P ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 L ) - 1 ) ) -> ( ( ( ( NTP4VCMin N ) <_ ( ( NTP4VCOffset N ) + ( -u 1 ) ) ) /\ ( ( ( NTP4VCOffset N ) + ( -u 1 ) ) <_ ( NTP4VCMax N ) ) ) /\ ( NTP4VCQ43 A B C D E F G H I J K L M N O P z ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I $.
  ntp4vc-q45-def $a |- ( NTP4VCQ45 A B C D E F G H I ) <-> A. z A. y ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( y e. ( NTP4VCPtr _V ) ) ) -> ( ( ( ( ( ( ( ( ( NTP4VCData z ) = ( NTP4VCData y ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData G ) ) ) ) /\ ( ( NTP4VCOffset z ) = ( NTP4VCOffset G ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin G ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax G ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable G ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone G ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData H ) ) ) /\ ( ( NTP4VCOffset y ) = ( NTP4VCOffset H ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin H ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax H ) ) ) /\ ( ( NTP4VCWritable y ) = ( NTP4VCWritable H ) ) ) /\ ( ( NTP4VCZone y ) = ( NTP4VCZone H ) ) ) -> ( ( ( ( NTP4VCMapBase z ) = ( NTP4VCMapUpdate ( NTP4VCMapBase G ) ( ( NTP4VCOffset z ) + 1 ) F ) ) /\ ( ( NTP4VCMapGet ( NTP4VCMapBase z ) ( ( NTP4VCOffset z ) + 1 ) ) = F ) ) -> ( ( ( ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( NTP4VCValue I ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) x. E ) ) x. ( NTP4VCValue D ( NTP4VCSigned32 A ) ) ) + ( NTP4VCValue y ( NTP4VCSigned32 A ) ) ) ) /\ ( ( NTP4VCValue y ( NTP4VCSigned32 A ) ) < ( NTP4VCValue D ( NTP4VCSigned32 A ) ) ) ) /\ ( 0 <_ E ) ) /\ ( E <_ 1 ) ) ) ) ) ) $.
$}
${
  $d z y x w v u e A B C D E F G H I J K L $.
  ntp4vc-q46-def $a |- ( NTP4VCQ46 A B C D E F G H I J K L ) <-> A. z A. y A. x A. w A. v A. u ( ( ( z e. NTP4VCWord64 ) /\ ( ( y e. NTP4VCWord32 ) /\ ( ( x e. ( NTP4VCPtr _V ) ) /\ ( ( w e. ( NTP4VCPtr _V ) ) /\ ( ( v e. ( NTP4VCPtr _V ) ) /\ ( u e. ( NTP4VCPtr _V ) ) ) ) ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData v ) ) = ( # ` ( NTP4VCData L ) ) ) /\ ( ( NTP4VCOffset v ) = ( NTP4VCOffset L ) ) ) /\ ( ( NTP4VCMin v ) = ( NTP4VCMin L ) ) ) /\ ( ( NTP4VCMax v ) = ( NTP4VCMax L ) ) ) /\ ( ( NTP4VCWritable v ) = ( NTP4VCWritable L ) ) ) /\ ( ( NTP4VCZone v ) = ( NTP4VCZone L ) ) ) -> ( ( ( ( ( ( ( ( # ` ( NTP4VCData u ) ) = ( # ` ( NTP4VCData E ) ) ) /\ ( ( NTP4VCOffset u ) = ( NTP4VCOffset E ) ) ) /\ ( ( NTP4VCMin u ) = ( NTP4VCMin E ) ) ) /\ ( ( NTP4VCMax u ) = ( NTP4VCMax E ) ) ) /\ ( ( NTP4VCWritable u ) = ( NTP4VCWritable E ) ) ) /\ ( ( NTP4VCZone u ) = ( NTP4VCZone E ) ) ) -> ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( 0 <_ ( NTP4VCSigned32 y ) ) /\ ( ( NTP4VCSigned32 y ) <_ ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) ) /\ ( ( NTP4VCOffset x ) = ( ( NTP4VCOffset u ) + ( NTP4VCSigned32 y ) ) ) ) /\ ( ( NTP4VCOffset w ) = ( ( ( ( NTP4VCOffset v ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 y ) ) - 2 ) ) ) /\ ( ( # ` ( NTP4VCData x ) ) = ( # ` ( NTP4VCData u ) ) ) ) /\ ( ( NTP4VCMin x ) = ( NTP4VCMin u ) ) ) /\ ( ( NTP4VCMax x ) = ( NTP4VCMax u ) ) ) /\ ( ( # ` ( NTP4VCData w ) ) = ( # ` ( NTP4VCData v ) ) ) ) /\ ( ( NTP4VCMin w ) = ( NTP4VCMin v ) ) ) /\ ( ( NTP4VCMax w ) = ( NTP4VCMax v ) ) ) /\ ( ( NTP4VCMapBase x ) = ( NTP4VCMapBase u ) ) ) /\ ( ( NTP4VCMapBase w ) = ( NTP4VCMapBase v ) ) ) /\ ( ( ( NTP4VCWritable x ) = 1 ) /\ ( ( NTP4VCWritable w ) = 1 ) ) ) /\ ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( ( ( NTP4VCValue x ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 y ) ) ) + ( K x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 y ) ) ) ) ) x. J ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 y ) ) ) + ( NTP4VCValue v ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 y ) ) - 1 ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 y ) ) - 1 ) ) x. z ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase v ) ( ( NTP4VCOffset w ) + ( NTP4VCSigned32 I ) ) ( ( ( ( NTP4VCOffset w ) + ( NTP4VCSigned32 I ) ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. z ) ) < J ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase v ) ( NTP4VCOffset w ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. z ) ) <_ ( G + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. F ) ) ) ) -> ( ( ( 0 < ( NTP4VCSigned32 y ) ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 y ) - 1 ) ) /\ ( NTP4VCQ44 A B C D F G H I J K z y x w v u ) ) ) /\ ( -. ( 0 < ( NTP4VCSigned32 y ) ) -> ( ( ( ( NTP4VCOffset v ) <_ ( NTP4VCOffset w ) ) /\ ( ( ( ( NTP4VCOffset w ) + 1 ) < ( NTP4VCOffset v ) ) \/ ( ( NTP4VCOffset w ) <_ ( ( NTP4VCOffset w ) + 1 ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase v ) ( NTP4VCOffset v ) ( NTP4VCOffset w ) ) = ( NTP4VCValueSub ( NTP4VCMapUpdate ( NTP4VCMapBase v ) ( ( NTP4VCOffset w ) + 1 ) z ) ( NTP4VCOffset v ) ( NTP4VCOffset w ) ) ) -> ( ( ( ( ( NTP4VCMin w ) <_ ( ( NTP4VCOffset w ) + 1 ) ) /\ ( ( ( NTP4VCOffset w ) + 1 ) < ( NTP4VCMax w ) ) ) /\ ( ( NTP4VCWritable w ) = 1 ) ) /\ ( NTP4VCQ45 A B C D K z w v u ) ) ) ) ) ) ) ) ) ) $.
$}
${
  $d z y x e A B C D E F G H I J K L M N O $.
  ntp4vc-q47-def $a |- ( NTP4VCQ47 A B C D E F G H I J K L M N O ) <-> A. z A. y ( ( ( z e. ( NTP4VCPtr _V ) ) /\ ( y e. ( NTP4VCPtr _V ) ) ) -> ( ( NTP4VCQ5 A C D F M O z y ) -> ( ( ( ( ( ( NTP4VCMin y ) <_ ( ( NTP4VCOffset y ) + 1 ) ) /\ ( ( ( NTP4VCOffset y ) + 1 ) < ( NTP4VCMax y ) ) ) /\ ( ( ( NTP4VCMin y ) <_ ( ( NTP4VCOffset y ) + 1 ) ) /\ ( ( ( NTP4VCOffset y ) + 1 ) < ( NTP4VCMax y ) ) ) ) /\ ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( 0 <_ ( NTP4VCSigned32 K ) ) /\ ( ( NTP4VCSigned32 K ) <_ ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) ) /\ ( ( NTP4VCOffset G ) = ( ( NTP4VCOffset E ) + ( NTP4VCSigned32 K ) ) ) ) /\ ( ( NTP4VCOffset y ) = ( ( ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 A ) ) + ( NTP4VCSigned32 K ) ) - 2 ) ) ) /\ ( ( # ` ( NTP4VCData G ) ) = ( # ` ( NTP4VCData E ) ) ) ) /\ ( ( NTP4VCMin G ) = ( NTP4VCMin E ) ) ) /\ ( ( NTP4VCMax G ) = ( NTP4VCMax E ) ) ) /\ ( ( # ` ( NTP4VCData y ) ) = ( # ` ( NTP4VCData z ) ) ) ) /\ ( ( NTP4VCMin y ) = ( NTP4VCMin z ) ) ) /\ ( ( NTP4VCMax y ) = ( NTP4VCMax z ) ) ) /\ ( ( NTP4VCMapBase G ) = ( NTP4VCMapBase E ) ) ) /\ ( ( NTP4VCMapBase y ) = ( NTP4VCMapBase z ) ) ) /\ ( ( ( NTP4VCWritable G ) = 1 ) /\ ( ( NTP4VCWritable y ) = 1 ) ) ) /\ ( ( NTP4VCValue C ( NTP4VCSigned32 B ) ) = ( ( ( ( ( ( NTP4VCValue G ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) + ( O x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) - ( NTP4VCSigned32 K ) ) ) ) ) x. N ) x. ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( NTP4VCSigned32 K ) ) ) + ( NTP4VCValue z ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( ( NTP4VCSigned32 A ) + ( NTP4VCSigned32 K ) ) - 1 ) ) x. ( NTP4VCMapGet ( NTP4VCMapBase y ) ( ( NTP4VCOffset y ) + 1 ) ) ) ) ) ) /\ ( ( ( NTP4VCValueSub ( NTP4VCMapBase z ) ( ( NTP4VCOffset y ) + ( NTP4VCSigned32 L ) ) ( ( ( ( NTP4VCOffset y ) + ( NTP4VCSigned32 L ) ) + ( NTP4VCSigned32 A ) ) - 1 ) ) + ( ( NTP4VCIPow ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) ( ( NTP4VCSigned32 A ) - 1 ) ) x. ( NTP4VCMapGet ( NTP4VCMapBase y ) ( ( NTP4VCOffset y ) + 1 ) ) ) ) < N ) ) /\ ( ( ( NTP4VCMapGet ( NTP4VCMapBase z ) ( NTP4VCOffset y ) ) + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. ( NTP4VCMapGet ( NTP4VCMapBase y ) ( ( NTP4VCOffset y ) + 1 ) ) ) ) <_ ( I + ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) x. H ) ) ) ) ) /\ ( NTP4VCQ46 A B C D E H I J L N O z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N O $.
  ntp4vc-q48-def $a |- ( NTP4VCQ48 A B C D E F G H I J K L M N O ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( ( ( 0 <_ ( NTP4VCSigned32 O ) ) -> ( z = 1 ) ) /\ ( -. ( 0 <_ ( NTP4VCSigned32 O ) ) -> ( z = 0 ) ) ) -> ( ( NTP4VCQ1 A D M z ) /\ ( NTP4VCQ47 A B C D E F G H I J K L M N z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L M N $.
  ntp4vc-q49-def $a |- ( NTP4VCQ49 A B C D E F G H I J K L M N ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( NTP4VCCompareInt ( NTP4VCValue M ( NTP4VCSigned32 A ) ) ( NTP4VCValue D ( NTP4VCSigned32 A ) ) ) ) -> ( NTP4VCQ48 A B C D E F G H I J K L M N z ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K L $.
  ntp4vc-q50-def $a |- ( NTP4VCQ50 A B C D E F G H I J K L ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset F ) + ( NTP4VCSigned32 L ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData F ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase F ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData F ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin F ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax F ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone F ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable F ) ) ) -> ( ( ( NTP4VCValid z ( NTP4VCSigned32 A ) ) /\ ( NTP4VCValid D ( NTP4VCSigned32 A ) ) ) /\ ( NTP4VCQ49 A B C D E F G H I J K L z ( NTP4VCValue D ( NTP4VCSigned32 A ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J K $.
  ntp4vc-q51-def $a |- ( NTP4VCQ51 A B C D E F G H I J K ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( 2 - ( NTP4VCSigned32 A ) ) ) -> ( ( ( ( NTP4VCMin F ) <_ ( ( NTP4VCOffset F ) + ( NTP4VCSigned32 z ) ) ) /\ ( ( ( NTP4VCOffset F ) + ( NTP4VCSigned32 z ) ) <_ ( NTP4VCMax F ) ) ) /\ ( NTP4VCQ50 A B C D E F G H I J K z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I J $.
  ntp4vc-q52-def $a |- ( NTP4VCQ52 A B C D E F G H I J ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) -> ( ( NTP4VCInt32InBounds ( 2 - ( NTP4VCSigned32 A ) ) ) /\ ( NTP4VCQ51 A B C D E F G H I J z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H I $.
  ntp4vc-q53-def $a |- ( NTP4VCQ53 A B C D E F G H I ) <-> A. z ( ( z e. NTP4VCWord64 ) -> ( ( NTP4VCReciprocal3By2 z H I ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) /\ ( NTP4VCQ52 A B C D E F G H I z ) ) ) ) $.
$}
${
  $d z e A B C D E F G H $.
  ntp4vc-q54-def $a |- ( NTP4VCQ54 A B C D E F G H ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 A ) - 2 ) ) -> ( ( ( ( NTP4VCMin D ) <_ ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) ) /\ ( ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) < ( NTP4VCMax D ) ) ) /\ ( ( ( |_ ` ( ( ( ( 2 ^ ; 6 4 ) - 1 ) + 1 ) / 2 ) ) <_ H ) /\ ( NTP4VCQ53 A B C D E F G H ( NTP4VCMapGet ( NTP4VCMapBase D ) ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G $.
  ntp4vc-q55-def $a |- ( NTP4VCQ55 A B C D E F G ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 A ) - 1 ) ) -> ( ( ( ( NTP4VCMin D ) <_ ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) ) /\ ( ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) < ( NTP4VCMax D ) ) ) /\ ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 A ) - 2 ) ) /\ ( NTP4VCQ54 A B C D E F G ( NTP4VCMapGet ( NTP4VCMapBase D ) ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 z ) ) ) ) ) ) ) ) $.
$}
${
  $d z e A B C D E F G $.
  ntp4vc-q56-def $a |- ( NTP4VCQ56 A B C D E F G ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset E ) + ( NTP4VCSigned32 G ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData E ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase E ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData E ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin E ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax E ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone E ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable E ) ) ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 A ) - 1 ) ) /\ ( NTP4VCQ55 A B C D E F z ) ) ) ) $.
$}
${
  $d z e A B C D E F $.
  ntp4vc-q57-def $a |- ( NTP4VCQ57 A B C D E F ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) -> ( ( ( ( NTP4VCMin E ) <_ ( ( NTP4VCOffset E ) + ( NTP4VCSigned32 z ) ) ) /\ ( ( ( NTP4VCOffset E ) + ( NTP4VCSigned32 z ) ) <_ ( NTP4VCMax E ) ) ) /\ ( NTP4VCQ56 A B C D E F z ) ) ) ) $.
$}
${
  $d z e A B C D E F $.
  ntp4vc-q58-def $a |- ( NTP4VCQ58 A B C D E F ) <-> A. z ( ( z e. ( NTP4VCPtr _V ) ) -> ( ( ( ( ( ( ( ( ( ( NTP4VCOffset z ) = ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 F ) ) ) /\ ( ( # ` ( NTP4VCData z ) ) = ( # ` ( NTP4VCData C ) ) ) ) /\ ( ( NTP4VCMapBase z ) = ( NTP4VCMapBase C ) ) ) /\ ( ( NTP4VCData z ) = ( NTP4VCData C ) ) ) /\ ( ( NTP4VCMin z ) = ( NTP4VCMin C ) ) ) /\ ( ( NTP4VCMax z ) = ( NTP4VCMax C ) ) ) /\ ( ( NTP4VCZone z ) = ( NTP4VCZone C ) ) ) /\ ( ( NTP4VCWritable z ) = ( NTP4VCWritable C ) ) ) -> ( ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) /\ ( NTP4VCQ57 A B C D E z ) ) ) ) $.
$}
${
  $d z e A B C D E $.
  ntp4vc-q59-def $a |- ( NTP4VCQ59 A B C D E ) <-> A. z ( ( z e. NTP4VCWord32 ) -> ( ( ( NTP4VCSigned32 z ) = ( ( NTP4VCSigned32 B ) - 2 ) ) -> ( ( ( ( NTP4VCMin C ) <_ ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 z ) ) ) /\ ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 z ) ) <_ ( NTP4VCMax C ) ) ) /\ ( NTP4VCQ58 A B C D E z ) ) ) ) $.
$}

${
  ntp4vc-sy-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-sx-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-x-ptr $e |- C e. ( NTP4VCPtr _V ) $.
  ntp4vc-y-ptr $e |- D e. ( NTP4VCPtr _V ) $.
  ntp4vc-q-ptr $e |- E e. ( NTP4VCPtr _V ) $.
  ntp4vc-fact0 $e |- 3 <_ ( NTP4VCSigned32 A ) $.
  ntp4vc-fact1 $e |- ( NTP4VCSigned32 A ) <_ ( NTP4VCSigned32 B ) $.
  ntp4vc-fact2 $e |- ( NTP4VCValid C ( NTP4VCSigned32 B ) ) $.
  ntp4vc-fact3 $e |- ( NTP4VCValid D ( NTP4VCSigned32 A ) ) $.
  ntp4vc-fact4 $e |- (
    NTP4VCValid E ( ( NTP4VCSigned32 B ) - ( NTP4VCSigned32 A ) ) ) $.
  ntp4vc-fact5 $e |- ( NTP4VCWritable E ) = 1 $.
  ntp4vc-fact6 $e |- ( NTP4VCWritable C ) = 1 $.
  ntp4vc-fact7 $e |- ( NTP4VCNormalized D A ) $.

  ntp4vc-div-sb-qr-vc $a |- (
    ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 B ) - 2 ) ) /\
    ( NTP4VCQ59 A B C D E ) ) $.
$}
