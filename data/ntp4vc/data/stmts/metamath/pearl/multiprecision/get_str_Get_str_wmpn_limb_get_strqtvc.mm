$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_limb_get_strqtvc: the loop
  verification condition for converting one 64-bit limb into little-endian
  base digits, including reciprocal division, byte storage, loop invariants,
  pointer frames, and the final digit-string contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Fixed-width words are represented by their complete unsigned integer
  carriers. Signed 32-bit interpretation is two's complement; bytes and limbs
  retain the unsigned UChar and uint64 interpretations of the Why3 source.
  Pointers are tuples of a finite byte sequence, integer offset and bounds, a
  writability bit, and an element of an arbitrary nonempty zone carrier.

  The predicates below are faithful definitional factorizations of the
  generated nested verification condition. Proposition-valued conditionals
  are expanded into their two guarded implications. The final declaration is
  Metamath's native unproved $a statement encoding; every preceding $a is
  syntax or a definition, and this database contains no $p proof declaration.
$)

$c
  NTP4VCWord8 NTP4VCWord32 NTP4VCWord64
  NTP4VCSigned32
  NTP4VCInt32InBounds NTP4VCUInt64InBounds
  NTP4VCToNat NTP4VCIPow NTP4VCEDiv
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCPelts
  NTP4VCValid NTP4VCAccess NTP4VCSameFrame NTP4VCUpdateLaw
  NTP4VCInBase NTP4VCSValueLeSub NTP4VCSValueLe NTP4VCFrame
  NTP4VCBaseInfo NTP4VCBase NTP4VCExp NTP4VCBigBase
  NTP4VCReciprocal
  NTP4VCStateInvariant NTP4VCLoopInvariant NTP4VCExit
  NTP4VCAfterSp2 NTP4VCAfterO3 NTP4VCAfterO2 NTP4VCAfterNr
  NTP4VCAfterQR NTP4VCAfterL NTP4VCAfterH NTP4VCAfterO1
  NTP4VCStep NTP4VCLoopBody
$.

ntp4vc-word8-syntax $a class NTP4VCWord8 $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syntax $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint64-bounds-syntax $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-ipow-syntax $a class ( NTP4VCIPow A B ) $.
ntp4vc-ediv-syntax $a class ( NTP4VCEDiv A B ) $.
ntp4vc-ptr-syntax $a class ( NTP4VCPtr A B ) $.
ntp4vc-data-syntax $a class ( NTP4VCData A ) $.
ntp4vc-offset-syntax $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syntax $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syntax $a class ( NTP4VCZone A ) $.
ntp4vc-pelts-syntax $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.
ntp4vc-access-syntax $a wff ( NTP4VCAccess A B ) $.
ntp4vc-same-frame-syntax $a wff ( NTP4VCSameFrame A B ) $.
ntp4vc-update-law-syntax $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-in-base-syntax $a wff ( NTP4VCInBase A B C D ) $.
ntp4vc-svalue-le-sub-syntax
  $a class ( NTP4VCSValueLeSub A B C D ) $.
ntp4vc-svalue-le-syntax $a class ( NTP4VCSValueLe A B C ) $.
ntp4vc-frame-syntax $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-base-info-syntax $a class NTP4VCBaseInfo $.
ntp4vc-base-syntax $a class ( NTP4VCBase A ) $.
ntp4vc-exp-syntax $a class ( NTP4VCExp A ) $.
ntp4vc-big-base-syntax $a class ( NTP4VCBigBase A ) $.
ntp4vc-reciprocal-syntax $a wff ( NTP4VCReciprocal A B ) $.
ntp4vc-state-invariant-syntax
  $a wff ( NTP4VCStateInvariant A B C D E F ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D E F G ) $.
ntp4vc-exit-syntax
  $a wff ( NTP4VCExit A B C D E F ) $.
ntp4vc-after-sp2-syntax
  $a wff ( NTP4VCAfterSp2 A B C D E F G H ) $.
ntp4vc-after-o3-syntax
  $a wff ( NTP4VCAfterO3 A B C D E F G H I J ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C D E F G H I J K L ) $.
ntp4vc-after-nr-syntax
  $a wff ( NTP4VCAfterNr A B C D E F G H I J K L ) $.
ntp4vc-after-qr-syntax
  $a wff ( NTP4VCAfterQR A B C D E F G H I J K L ) $.
ntp4vc-after-l-syntax
  $a wff ( NTP4VCAfterL A B C D E F G H I J K L M ) $.
ntp4vc-after-h-syntax
  $a wff ( NTP4VCAfterH A B C D E F G H I J K L ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E F G H I J K L ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H I J K ) $.
ntp4vc-loop-body-syntax
  $a wff ( NTP4VCLoopBody A B C D E F G H I J K ) $.

ntp4vc-word8-definition $a |- NTP4VCWord8 =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- ( NTP4VCSigned32 A ) =
  if ( A < ( 2 ^ ; 3 1 ) , A , ( A - ( 2 ^ ; 3 2 ) ) ) $.

ntp4vc-int32-bounds-definition $a |- ( NTP4VCInt32InBounds A ) <-> (
  A e. ZZ /\
  ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) )
) $.

ntp4vc-uint64-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. NTP4VCWord64
) $.

ntp4vc-to-nat-definition $a |- ( NTP4VCToNat A ) =
  if ( 0 <_ A , A , 0 ) $.

ntp4vc-ipow-definition $a |- ( NTP4VCIPow A B ) =
  ( A ^ ( NTP4VCToNat B ) ) $.

ntp4vc-ediv-definition $a |- ( NTP4VCEDiv A B ) =
  ( |_ ` ( A / B ) ) $.

ntp4vc-ptr-definition $a |- ( NTP4VCPtr A B ) = (
  ( Word A ) X. ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. B ) ) ) )
) $.

ntp4vc-data-definition $a |- ( NTP4VCData A ) = ( 1st ` A ) $.

ntp4vc-offset-definition $a |- ( NTP4VCOffset A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-definition $a |- ( NTP4VCMin A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-definition $a |- ( NTP4VCMax A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-writable-definition $a |- ( NTP4VCWritable A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-zone-definition $a |- ( NTP4VCZone A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-pelts-definition $a |- ( NTP4VCPelts A B ) = if (
  ( NTP4VCToNat B ) < ( # ` ( NTP4VCData A ) ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-valid-definition $a |- ( NTP4VCValid A B ) <-> (
  ( NTP4VCInt32InBounds B ) /\
  ( 0 <_ B /\
    ( ( 0 <_ ( NTP4VCMin A ) /\ ( NTP4VCMin A ) <_ ( NTP4VCOffset A ) ) /\
      ( ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A ) /\
        ( NTP4VCMax A ) <_ ( # ` ( NTP4VCData A ) ) ) ) )
) $.

ntp4vc-access-definition $a |- ( NTP4VCAccess A B ) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B ) /\
  ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A )
) $.

ntp4vc-same-frame-definition $a |- ( NTP4VCSameFrame A B ) <-> (
  ( # ` ( NTP4VCData A ) ) = ( # ` ( NTP4VCData B ) ) /\
  ( ( NTP4VCOffset A ) = ( NTP4VCOffset B ) /\
    ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
      ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
        ( ( NTP4VCWritable A ) = ( NTP4VCWritable B ) /\
          ( NTP4VCZone A ) = ( NTP4VCZone B ) ) ) ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D
  ) <-> (
    A. x e. ZZ
      (
        ( NTP4VCPelts A x )
        =
        if ( x = C , D , ( NTP4VCPelts B x ) )
      )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $.

  ntp4vc-in-base-definition $a |- (
    NTP4VCInBase A B C D
  ) <-> (
    A. x e. ZZ
      (
        ( C <_ x /\ x < D )
        ->
        (
          0 <_ ( NTP4VCPelts B x )
          /\
          ( NTP4VCPelts B x ) < A
        )
      )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $.

  ntp4vc-svalue-le-sub-definition $a |- (
    NTP4VCSValueLeSub A B C D
  ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat ( D - C ) ) )
      (
        ( A ^ x )
        x.
        ( NTP4VCPelts B ( C + x ) )
      )
  ) $.
$}

ntp4vc-svalue-le-definition $a |- (
  NTP4VCSValueLe A B C
) = (
  NTP4VCSValueLeSub A B
    ( NTP4VCOffset B )
    ( ( NTP4VCOffset B ) + C )
) $.

${
  $d x A $. $d x B $. $d x C $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C
  ) <-> (
    A. x e. ZZ
      (
        (
          x < ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + C ) <_ x
        )
        ->
        ( NTP4VCPelts A x ) = ( NTP4VCPelts B x )
      )
  ) $.
$}

ntp4vc-base-info-definition $a |- NTP4VCBaseInfo = {
  x e. ( ZZ X. ( NTP4VCWord32 X. NTP4VCWord64 ) )
  |
  (
    ( 2 <_ ( 1st ` x ) /\ ( 1st ` x ) <_ ; 2 5 6 )
    /\
    (
      ( 7 <_ ( 1st ` ( 2nd ` x ) ) /\
        ( 1st ` ( 2nd ` x ) ) <_ ; 6 3 )
      /\
      (
        ( 2 ^ ; 6 4 ) <_
          ( ( 2nd ` ( 2nd ` x ) ) x. ( 1st ` x ) )
        /\
        ( 2nd ` ( 2nd ` x ) ) =
          ( NTP4VCIPow ( 1st ` x ) ( 1st ` ( 2nd ` x ) ) )
      )
    )
  )
} $.

ntp4vc-base-definition $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.

ntp4vc-exp-definition $a |- ( NTP4VCExp A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-big-base-definition $a |- ( NTP4VCBigBase A ) =
  ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-reciprocal-definition $a |- ( NTP4VCReciprocal A B ) <-> (
  A =
  (
    ( |_ `
      (
        (
          ( ( 2 ^ ; 6 4 ) x. ( 2 ^ ; 6 4 ) )
          -
          1
        )
        /
        B
      )
    )
    -
    ( 2 ^ ; 6 4 )
  )
) $.

ntp4vc-state-invariant-definition $a |- (
  NTP4VCStateInvariant A B C D E F
) <-> (
  (
    ( 0 <_ F /\ F < ( 2 ^ ; 6 4 ) )
    /\
    ( 0 <_ ( NTP4VCSigned32 E ) /\
      ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 C ) )
  )
  /\
  (
    (
      0 < F
      ->
      ( 0 <_ ( NTP4VCSigned32 E ) /\
        ( NTP4VCSigned32 E ) < ( NTP4VCSigned32 C ) )
    )
    /\
    (
      NTP4VCInBase A D
        ( NTP4VCOffset D )
        ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E ) )
    )
  )
  /\
  (
    (
      F = 0
      ->
      (
        0 < ( NTP4VCSigned32 E )
        ->
        0 <
          (
            NTP4VCPelts D
              (
                ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E ) )
                -
                1
              )
          )
      )
    )
    /\
    (
      B =
      (
        ( NTP4VCSValueLe A D ( NTP4VCSigned32 E ) )
        +
        ( ( NTP4VCIPow A ( NTP4VCSigned32 E ) ) x. F )
      )
    )
  )
) $.

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D E F G
) <-> (
  ( NTP4VCStateInvariant A C D E F G )
  /\
  ( NTP4VCFrame E B ( NTP4VCSigned32 F ) )
) $.

${
  $d r A $. $d r B $. $d r C $.
  $d r D $. $d r E $. $d r F $.

  ntp4vc-exit-definition $a |- (
    NTP4VCExit A B C D E F
  ) <-> (
    0 <_ ( NTP4VCSigned32 E )
    /\
    A. r e. NTP4VCWord32
      (
        r = ( NTP4VCSigned32 E )
        ->
        (
          ( NTP4VCSValueLe A F r ) = C
          /\
          ( 0 <_ r /\ r <_ ( NTP4VCSigned32 D ) )
        )
        /\
        (
          (
            0 < r
            ->
            0 <
              (
                NTP4VCPelts F
                  ( ( ( NTP4VCOffset F ) + r ) - 1 )
              )
          )
          /\
          (
            ( NTP4VCFrame F B r )
            /\
            (
              NTP4VCInBase A F
                ( NTP4VCOffset F )
                ( ( NTP4VCOffset F ) + r )
            )
          )
        )
      )
  ) $.
$}

${
  $d o A $. $d o B $. $d o C $. $d o D $.
  $d o E $. $d o F $. $d o G $. $d o H $.

  ntp4vc-after-sp2-definition $a |- (
    NTP4VCAfterSp2 A B C D E F G H
  ) <-> (
    ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 E ) + 1 ) )
    /\
    A. o e. NTP4VCWord32
      (
        ( NTP4VCSigned32 o ) = ( ( NTP4VCSigned32 E ) + 1 )
        ->
        (
          G < F
          /\
          ( NTP4VCLoopInvariant A B C D H o G )
        )
      )
  ) $.
$}

${ 
  $d p A $. $d p B $. $d p C $. $d p D $. $d p E $.
  $d p F $. $d p G $. $d p H $. $d p I $. $d p J $.

  ntp4vc-after-o3-definition $a |- (
    NTP4VCAfterO3 A B C D E F G H I J
  ) <-> (
    (
      ( NTP4VCAccess G ( NTP4VCSigned32 E ) )
      /\
      ( NTP4VCWritable G ) = 1
    )
    /\
    A. p e. ( NTP4VCPtr NTP4VCWord8 J )
      (
        ( NTP4VCSameFrame p G )
        ->
        (
          (
            ( NTP4VCUpdateLaw p G
              ( ( NTP4VCOffset p ) + ( NTP4VCSigned32 E ) ) I )
            /\
            (
              NTP4VCPelts p
                ( ( NTP4VCOffset p ) + ( NTP4VCSigned32 E ) )
            )
            =
            I
          )
          ->
          ( NTP4VCAfterSp2 A B C D E F H p )
        )
      )
  ) $.
$}

${
  $d o A $. $d o B $. $d o C $. $d o D $. $d o E $.
  $d o F $. $d o G $. $d o H $. $d o I $. $d o J $. $d o K $.
  $d o L $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C D E F G H I J K L
  ) <-> (
    ( 0 <_ K /\ K <_ ; 2 5 5 )
    /\
    A. o e. NTP4VCWord8
      (
        o = K
        ->
        ( NTP4VCAfterO3 A B C D E F G H o L )
      )
  ) $.
$}

${
  $d o A $. $d o B $. $d o C $. $d o D $. $d o E $.
  $d o F $. $d o G $. $d o H $. $d o I $. $d o J $. $d o K $.
  $d o L $.

  ntp4vc-after-nr-definition $a |- (
    NTP4VCAfterNr A B C D E F G H I J K L
  ) <-> (
    (
      ( 0 <_ J /\ J < ; 6 4 )
      /\
      ( I mod ( NTP4VCIPow 2 J ) ) = 0
    )
    /\
    A. o e. NTP4VCWord64
      (
        I = ( ( NTP4VCIPow 2 J ) x. o )
        ->
        ( NTP4VCAfterO2 A B C D E F G H I J o L )
      )
  ) $.
$}

${
  $d n A $. $d n B $. $d n C $. $d n D $. $d n E $.
  $d n F $. $d n G $. $d n H $. $d n I $. $d n J $. $d n K $.
  $d n L $.

  ntp4vc-after-qr-definition $a |- (
    NTP4VCAfterQR A B C D E F G H I J K L
  ) <-> (
    (
      ( 0 <_ E /\ E < ; 6 4 )
      /\
      ( K mod ( NTP4VCIPow 2 E ) ) = 0
    )
    /\
    A. n e. NTP4VCWord64
      (
        K = ( ( NTP4VCIPow 2 E ) x. n )
        ->
        ( NTP4VCAfterNr A B C F G H I J K E n L )
      )
  ) $.
$}

${
  $d q A $. $d q B $. $d q C $. $d q D $. $d q E $. $d q F $.
  $d q G $. $d q H $. $d q I $. $d q J $. $d q K $. $d q L $.
  $d q M $.
  $d r A $. $d r B $. $d r C $. $d r D $. $d r E $. $d r F $.
  $d r G $. $d r H $. $d r I $. $d r J $. $d r K $. $d r L $.
  $d r M $.
  $d q r $.

  ntp4vc-after-l-definition $a |- (
    NTP4VCAfterL A B C D E F G H I J K L M
  ) <-> (
    (
      ( ( ( 2 ^ ; 6 4 ) / 2 ) <_ D /\ K < D )
      /\
      ( NTP4VCReciprocal F D )
    )
    /\
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              ( ( q x. D ) + r )
              =
              ( L + ( ( 2 ^ ; 6 4 ) x. K ) )
            )
            /\
            ( 0 <_ r /\ r < D )
          )
          ->
          ( NTP4VCAfterQR A B C D E G H I J q r M )
        )
  ) $.
$}

${
  $d l A $. $d l B $. $d l C $. $d l D $. $d l E $. $d l F $.
  $d l G $. $d l H $. $d l I $. $d l J $. $d l K $. $d l L $.

  ntp4vc-after-h-definition $a |- (
    NTP4VCAfterH A B C D E F G H I J K L
  ) <-> (
    ( 0 <_ E /\ E < ; 6 4 )
    /\
    A. l e. NTP4VCWord64
      (
        l =
          ( ( I x. ( NTP4VCIPow 2 E ) ) mod ( 2 ^ ; 6 4 ) )
        ->
        ( NTP4VCAfterL A B C D E F G H I J K l L )
      )
  ) $.
$}

${
  $d h A $. $d h B $. $d h C $. $d h D $. $d h E $. $d h F $.
  $d h G $. $d h H $. $d h I $. $d h J $. $d h K $. $d h L $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E F G H I J K L
  ) <-> (
    ( 0 <_ K /\ K < ; 6 4 )
    /\
    A. h e. NTP4VCWord64
      (
        h = ( NTP4VCEDiv I ( NTP4VCIPow 2 K ) )
        ->
        ( NTP4VCAfterH A B C D E F G H I J h L )
      )
  ) $.
$}

${
  $d o A $. $d o B $. $d o C $. $d o D $. $d o E $.
  $d o F $. $d o G $. $d o H $. $d o I $. $d o J $. $d o K $.

  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E F G H I J K
  ) <-> (
    ( NTP4VCUInt64InBounds ( ; 6 4 - E ) )
    /\
    A. o e. NTP4VCWord64
      (
        o = ( ; 6 4 - E )
        ->
        ( NTP4VCAfterO1 A B C D E F G H I J o K )
      )
  ) $.
$}

ntp4vc-loop-body-definition $a |- (
  NTP4VCLoopBody A B C D E F G H I J K
) <-> (
  (
    0 < I
    ->
    ( NTP4VCStep A B C D E F G H I J K )
  )
  /\
  (
    -. 0 < I
    ->
    ( NTP4VCExit A B C G H J )
  )
) $.

${
  $( Source parameters:
     A=binfo, B=sp, C=d1, D=shift, E=di, F=sz, G=w, Z=zone. $)

  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-binfo-type $e |- A e. NTP4VCBaseInfo $.
  ntp4vc-sp-type $e |- B e. ( NTP4VCPtr NTP4VCWord8 Z ) $.
  ntp4vc-d1-type $e |- C e. NTP4VCWord64 $.
  ntp4vc-shift-type $e |- D e. NTP4VCWord64 $.
  ntp4vc-di-type $e |- E e. NTP4VCWord64 $.
  ntp4vc-sz-type $e |- F e. NTP4VCWord32 $.
  ntp4vc-w-type $e |- G e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- 2 <_ ( NTP4VCBase A ) $.
  ntp4vc-fact1 $e |- ( NTP4VCBase A ) <_ ; 2 5 6 $.
  ntp4vc-fact2 $e |- ( NTP4VCWritable B ) = 1 $.
  ntp4vc-fact3 $e |- ( ( 2 ^ ; 6 4 ) / 2 ) <_ C $.
  ntp4vc-fact4 $e |- 0 <_ D $.
  ntp4vc-fact5 $e |- D <_ ; 6 3 $.
  ntp4vc-fact6 $e |- (
    ( NTP4VCBase A ) x. ( NTP4VCIPow 2 D )
  ) = C $.
  ntp4vc-fact7 $e |- ( NTP4VCReciprocal E C ) $.
  ntp4vc-fact8 $e |- ( NTP4VCValid B ( NTP4VCSigned32 F ) ) $.
  ntp4vc-fact9 $e |- 0 < ( NTP4VCSigned32 F ) $.
  ntp4vc-fact10 $e |- G <
    ( NTP4VCIPow ( NTP4VCBase A ) ( NTP4VCSigned32 F ) ) $.

  $d i A $. $d i B $. $d i C $. $d i D $. $d i E $.
  $d i F $. $d i G $. $d i Z $.
  $d w A $. $d w B $. $d w C $. $d w D $. $d w E $.
  $d w F $. $d w G $. $d w Z $.
  $d p A $. $d p B $. $d p C $. $d p D $. $d p E $.
  $d p F $. $d p G $. $d p Z $.
  $d i w p $.

  ntp4vc-pearl-multiprecision-get-str-wmpn-limb-get-str-vc $a |- (
    (
      NTP4VCStateInvariant
        ( NTP4VCBase A ) G F B 0 G
    )
    /\
    A. i e. NTP4VCWord32
      A. w e. NTP4VCWord64
        A. p e. ( NTP4VCPtr NTP4VCWord8 Z )
          (
            ( NTP4VCSameFrame p B )
            ->
            (
              ( NTP4VCLoopInvariant
                ( NTP4VCBase A ) B G F p i w )
              ->
              (
                NTP4VCLoopBody
                  ( NTP4VCBase A ) B G C D E F i w p Z
              )
            )
          )
  ) $.
$}
