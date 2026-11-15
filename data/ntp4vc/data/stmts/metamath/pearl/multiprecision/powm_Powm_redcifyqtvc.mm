$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_redcifyqtvc: the verification condition for
  converting a multiprecision integer to radix-2^64 Montgomery form by
  zero-extension, copying into a shifted pointer view, and
  quotient-remainder division. This file contains no proof.

  Unsigned 32- and 64-bit words are represented by their complete bounded
  integer carriers, and signed 32-bit values use exact two's-complement
  interpretation. A pointer retains the source finite limb sequence, integer
  offset and bounds, Boolean writability field, and arbitrary nonempty zone.
  NTP4VCValue definitionally renders the source little-endian radix-2^64
  value function. The helper predicates below are explicit definitional
  abbreviations for the source's nested universal quantifiers, implications,
  allocation descriptions, pointer frames, copy relation, division equation,
  and modular postconditions.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCPlength NTP4VCOffset NTP4VCMin
  NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts
  NTP4VCPeltsEq NTP4VCValid NTP4VCValue NTP4VCIPow NTP4VCRedc
  NTP4VCAllocation NTP4VCSameMeta NTP4VCOutsideFrame
  NTP4VCShiftedPointer NTP4VCMapEqSubShift NTP4VCCopyOutputs
  NTP4VCDivisionResult NTP4VCPostcondition NTP4VCAfterFinalPointers
  NTP4VCDivisionFacts NTP4VCAfterO7 NTP4VCAfterCopy
  NTP4VCAfterO5 NTP4VCAfterTp1 NTP4VCAfterQp NTP4VCAfterO4
  NTP4VCAfterO3 NTP4VCAfterTp NTP4VCAfterO2 NTP4VCAfterO1
$.

$v o1 o2 tp o3 o4 qp tp1 o5 o6 tp2 o7 qp1 rp1 $.

ntp4vc-o1-variable $f setvar o1 $.
ntp4vc-o2-variable $f setvar o2 $.
ntp4vc-tp-variable $f setvar tp $.
ntp4vc-o3-variable $f setvar o3 $.
ntp4vc-o4-variable $f setvar o4 $.
ntp4vc-qp-variable $f setvar qp $.
ntp4vc-tp1-variable $f setvar tp1 $.
ntp4vc-o5-variable $f setvar o5 $.
ntp4vc-o6-variable $f setvar o6 $.
ntp4vc-tp2-variable $f setvar tp2 $.
ntp4vc-o7-variable $f setvar o7 $.
ntp4vc-qp1-variable $f setvar qp1 $.
ntp4vc-rp1-variable $f setvar rp1 $.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-ptr-syntax $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syntax $a class ( NTP4VCData A ) $.
ntp4vc-plength-syntax $a class ( NTP4VCPlength A ) $.
ntp4vc-offset-syntax $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syntax $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syntax $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syntax $a class ( NTP4VCPelts A B ) $.
ntp4vc-pelts-eq-syntax $a wff ( NTP4VCPeltsEq A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-ipow-syntax $a class ( NTP4VCIPow A B ) $.
ntp4vc-redc-syntax $a wff ( NTP4VCRedc A B C D ) $.
ntp4vc-allocation-syntax $a wff ( NTP4VCAllocation A B ) $.
ntp4vc-same-meta-syntax $a wff ( NTP4VCSameMeta A B ) $.
ntp4vc-outside-frame-syntax
  $a wff ( NTP4VCOutsideFrame A B C ) $.
ntp4vc-shifted-pointer-syntax
  $a wff ( NTP4VCShiftedPointer A B C ) $.
ntp4vc-map-eq-sub-shift-syntax
  $a wff ( NTP4VCMapEqSubShift A B C D E ) $.
ntp4vc-copy-outputs-syntax
  $a wff ( NTP4VCCopyOutputs A B C ) $.
ntp4vc-division-result-syntax
  $a wff ( NTP4VCDivisionResult A B C D E F ) $.
ntp4vc-postcondition-syntax
  $a wff ( NTP4VCPostcondition A B C D E ) $.
ntp4vc-after-final-pointers-syntax
  $a wff ( NTP4VCAfterFinalPointers A B C D E F G H I ) $.
ntp4vc-division-facts-syntax
  $a wff ( NTP4VCDivisionFacts A B C D E F G H I ) $.
ntp4vc-after-o7-syntax
  $a wff ( NTP4VCAfterO7 A B C D E F G H ) $.
ntp4vc-after-copy-syntax
  $a wff ( NTP4VCAfterCopy A B C D E F G H I ) $.
ntp4vc-after-o5-syntax
  $a wff ( NTP4VCAfterO5 A B C D E F G H ) $.
ntp4vc-after-tp1-syntax
  $a wff ( NTP4VCAfterTp1 A B C D E F G H ) $.
ntp4vc-after-qp-syntax
  $a wff ( NTP4VCAfterQp A B C D E F G H ) $.
ntp4vc-after-o4-syntax
  $a wff ( NTP4VCAfterO4 A B C D E F G H ) $.
ntp4vc-after-o3-syntax
  $a wff ( NTP4VCAfterO3 A B C D E F G ) $.
ntp4vc-after-tp-syntax
  $a wff ( NTP4VCAfterTp A B C D E F G ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C D E F G ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E F ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- (
  NTP4VCSigned32 A
) = if (
  A < ( 2 ^ ; 3 1 ) ,
  A ,
  ( A - ( 2 ^ ; 3 2 ) )
) $.

ntp4vc-int32-in-bounds-definition $a |- (
  NTP4VCInt32InBounds A
) <-> (
  A e. ZZ
  /\
  (
    ( -u ( 2 ^ ; 3 1 ) ) <_ A
    /\
    A < ( 2 ^ ; 3 1 )
  )
) $.

ntp4vc-ptr-definition $a |- (
  NTP4VCPtr A
) = (
  ( Word NTP4VCWord64 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) )
) $.

ntp4vc-data-definition $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-plength-definition $a |- (
  NTP4VCPlength A
) = ( # ` ( NTP4VCData A ) ) $.

ntp4vc-offset-definition $a |- (
  NTP4VCOffset A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-writable-definition $a |- (
  NTP4VCWritable A
) = (
  1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
) $.

ntp4vc-zone-definition $a |- (
  NTP4VCZone A
) = (
  2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-pelts-definition $a |- (
  NTP4VCPelts A B
) = if (
  ( NTP4VCToNat B ) < ( NTP4VCPlength A ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d j A B $.

  ntp4vc-pelts-eq-definition $a |- (
    NTP4VCPeltsEq A B
  ) <-> (
    A. j e. ZZ
      ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
  ) $.
$}

ntp4vc-valid-definition $a |- (
  NTP4VCValid A B
) <-> (
  ( NTP4VCInt32InBounds B )
  /\
  (
    0 <_ B
    /\
    (
      (
        0 <_ ( NTP4VCMin A )
        /\
        ( NTP4VCMin A ) <_ ( NTP4VCOffset A )
      )
      /\
      (
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A )
        /\
        ( NTP4VCMax A ) <_ ( NTP4VCPlength A )
      )
    )
  )
) $.

${
  $d k A B $.

  ntp4vc-value-definition $a |- (
    NTP4VCValue A B
  ) = (
    sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
      (
        ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) )
        x.
        ( ( 2 ^ ; 6 4 ) ^ k )
      )
  ) $.
$}

ntp4vc-ipow-definition $a |- (
  NTP4VCIPow A B
) = ( A ^ ( NTP4VCToNat B ) ) $.

ntp4vc-redc-definition $a |- (
  NTP4VCRedc A B C D
) <-> (
  ( A mod D )
  =
  ( ( ( NTP4VCIPow ( 2 ^ ; 6 4 ) C ) x. B ) mod D )
) $.

ntp4vc-allocation-definition $a |- (
  NTP4VCAllocation A B
) <-> (
  ( NTP4VCPlength A ) = B
  /\
  (
    ( NTP4VCOffset A ) = 0
    /\
    (
      ( NTP4VCMin A ) = 0
      /\
      (
        ( NTP4VCMax A ) = B
        /\
        ( NTP4VCWritable A ) = 1
      )
    )
  )
) $.

ntp4vc-same-meta-definition $a |- (
  NTP4VCSameMeta A B
) <-> (
  ( NTP4VCPlength A ) = ( NTP4VCPlength B )
  /\
  (
    ( NTP4VCOffset A ) = ( NTP4VCOffset B )
    /\
    (
      ( NTP4VCMin A ) = ( NTP4VCMin B )
      /\
      (
        ( NTP4VCMax A ) = ( NTP4VCMax B )
        /\
        (
          ( NTP4VCWritable A ) = ( NTP4VCWritable B )
          /\
          ( NTP4VCZone A ) = ( NTP4VCZone B )
        )
      )
    )
  )
) $.

${
  $d j A B C $.

  ntp4vc-outside-frame-definition $a |- (
    NTP4VCOutsideFrame A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          j < ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + C ) <_ j
        )
        ->
        ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
      )
  ) $.
$}

ntp4vc-shifted-pointer-definition $a |- (
  NTP4VCShiftedPointer A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( NTP4VCPlength A ) = ( NTP4VCPlength B )
    /\
    (
      ( NTP4VCPeltsEq A B )
      /\
      (
        ( NTP4VCData A ) = ( NTP4VCData B )
        /\
        (
          ( NTP4VCMin A ) = ( NTP4VCMin B )
          /\
          (
            ( NTP4VCMax A ) = ( NTP4VCMax B )
            /\
            (
              ( NTP4VCZone A ) = ( NTP4VCZone B )
              /\
              ( NTP4VCWritable A ) = ( NTP4VCWritable B )
            )
          )
        )
      )
    )
  )
) $.

${
  $d i A B C D E $.

  ntp4vc-map-eq-sub-shift-definition $a |- (
    NTP4VCMapEqSubShift A B C D E
  ) <-> (
    A. i e. ZZ
      (
        ( 0 <_ i /\ i < E )
        ->
        ( NTP4VCPelts A ( C + i ) )
        =
        ( NTP4VCPelts B ( D + i ) )
      )
  ) $.
$}

ntp4vc-copy-outputs-definition $a |- (
  NTP4VCCopyOutputs A B C
) <-> (
  ( NTP4VCData A ) = ( NTP4VCData B )
  /\
  (
    ( NTP4VCPlength B ) = ( NTP4VCPlength C )
    /\
    (
      ( NTP4VCOffset A ) = ( NTP4VCOffset C )
      /\
      (
        ( NTP4VCMin A ) = ( NTP4VCMin C )
        /\
        (
          ( NTP4VCMax A ) = ( NTP4VCMax C )
          /\
          (
            ( NTP4VCWritable A ) = ( NTP4VCWritable C )
            /\
            ( NTP4VCZone A ) = ( NTP4VCZone C )
          )
        )
      )
    )
  )
) $.

ntp4vc-division-result-definition $a |- (
  NTP4VCDivisionResult A B C D E F
) <-> (
  ( NTP4VCValue A E )
  =
  (
    (
      ( NTP4VCValue B ( ( E - F ) + 1 ) )
      x.
      ( NTP4VCValue D F )
    )
    +
    ( NTP4VCValue C F )
  )
  /\
  ( NTP4VCValue C F ) < ( NTP4VCValue D F )
) $.

ntp4vc-postcondition-definition $a |- (
  NTP4VCPostcondition A B C D E
) <-> (
  ( NTP4VCValue A E )
  =
  (
    (
      ( NTP4VCIPow ( 2 ^ ; 6 4 ) E )
      x.
      ( NTP4VCValue B C )
    )
    mod
    ( NTP4VCValue D E )
  )
  /\
  (
    NTP4VCRedc
      ( NTP4VCValue A E )
      ( NTP4VCValue B C )
      E
      ( NTP4VCValue D E )
  )
) $.

${
  $d qp1 rp1 $.
  $d qp1 A B C D E F G H I $.
  $d rp1 A B C D E F G H I $.

  ntp4vc-after-final-pointers-definition $a |- (
    NTP4VCAfterFinalPointers A B C D E F G H I
  ) <-> (
    A. qp1 e. ( NTP4VCPtr I )
      A. rp1 e. ( NTP4VCPtr I )
        (
          ( NTP4VCSameMeta qp1 A )
          ->
          (
            ( NTP4VCSameMeta rp1 B )
            ->
            (
              ( NTP4VCDivisionResult C qp1 rp1 D E H )
              ->
              ( NTP4VCPostcondition rp1 F G D H )
            )
          )
        )
  ) $.
$}

ntp4vc-division-facts-definition $a |- (
  NTP4VCDivisionFacts A B C D E F G H I
) <-> (
  (
    (
      (
        1 <_ ( NTP4VCSigned32 G )
        /\
        ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 F )
      )
      /\
      (
        ( NTP4VCSigned32 F )
        <_
        ( ( ( 2 ^ ; 3 1 ) - 1 ) - 1 )
      )
    )
    /\
    (
      ( NTP4VCValid A ( NTP4VCSigned32 F ) )
      /\
      (
        ( NTP4VCValid B ( NTP4VCSigned32 G ) )
        /\
        (
          (
            NTP4VCValid C
              (
                (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 G )
                )
                +
                1
              )
          )
          /\
          (
            ( NTP4VCValid D ( NTP4VCSigned32 G ) )
            /\
            (
              (
                ( NTP4VCWritable C ) = 1
                /\
                ( NTP4VCWritable D ) = 1
              )
              /\
              (
                0
                <
                (
                  NTP4VCPelts B
                    (
                      (
                        ( NTP4VCOffset B )
                        +
                        ( NTP4VCSigned32 G )
                      )
                      -
                      1
                    )
                )
              )
            )
          )
        )
      )
    )
  )
  /\
  (
    NTP4VCAfterFinalPointers
      C D A B ( NTP4VCSigned32 F ) E
      ( NTP4VCSigned32 H ) ( NTP4VCSigned32 G ) I
  )
) $.

${
  $d o7 A B C D E F G H $.

  ntp4vc-after-o7-definition $a |- (
    NTP4VCAfterO7 A B C D E F G H
  ) <-> (
    A. o7 e. NTP4VCWord32
      (
        (
          ( NTP4VCSigned32 o7 )
          =
          (
            ( NTP4VCSigned32 G )
            +
            ( NTP4VCSigned32 F )
          )
        )
        ->
        ( NTP4VCDivisionFacts A B C D E o7 F G H )
      )
  ) $.
$}

${
  $d o6 tp2 $.
  $d o6 A B C D E F G H I $.
  $d tp2 A B C D E F G H I $.

  ntp4vc-after-copy-definition $a |- (
    NTP4VCAfterCopy A B C D E F G H I
  ) <-> (
    A. o6 e. ( NTP4VCPtr I )
      A. tp2 e. ( NTP4VCPtr I )
        (
          ( NTP4VCCopyOutputs o6 tp2 A )
          ->
          (
            ( NTP4VCSameMeta tp2 B )
            ->
            (
              (
                (
                  NTP4VCMapEqSubShift
                    o6 C
                    ( NTP4VCOffset o6 )
                    ( NTP4VCOffset C )
                    ( NTP4VCSigned32 H )
                )
                /\
                (
                  NTP4VCOutsideFrame
                    o6 A ( NTP4VCSigned32 H )
                )
              )
              ->
              (
                (
                  NTP4VCInt32InBounds
                    (
                      ( NTP4VCSigned32 H )
                      +
                      ( NTP4VCSigned32 G )
                    )
                )
                /\
                ( NTP4VCAfterO7 tp2 D E F C G H I )
              )
            )
          )
        )
  ) $.
$}

${
  $d o5 A B C D E F G H $.

  ntp4vc-after-o5-definition $a |- (
    NTP4VCAfterO5 A B C D E F G H
  ) <-> (
    A. o5 e. ( NTP4VCPtr H )
      (
        (
          NTP4VCShiftedPointer
            o5 A ( NTP4VCSigned32 F )
        )
        ->
        (
          (
            ( NTP4VCValid B ( NTP4VCSigned32 G ) )
            /\
            (
              ( NTP4VCValid o5 ( NTP4VCSigned32 G ) )
              /\
              ( NTP4VCWritable o5 ) = 1
            )
          )
          /\
          ( NTP4VCAfterCopy o5 A B C D E F G H )
        )
      )
  ) $.
$}

${
  $d tp1 A B C D E F G H $.

  ntp4vc-after-tp1-definition $a |- (
    NTP4VCAfterTp1 A B C D E F G H
  ) <-> (
    A. tp1 e. ( NTP4VCPtr H )
      (
        ( NTP4VCSameMeta tp1 A )
        ->
        (
          (
            ( NTP4VCValue tp1 ( NTP4VCSigned32 F ) ) = 0
            /\
            (
              NTP4VCOutsideFrame
                tp1 A ( NTP4VCSigned32 F )
            )
          )
          ->
          (
            (
              ( NTP4VCMin tp1 )
              <_
              (
                ( NTP4VCOffset tp1 )
                +
                ( NTP4VCSigned32 F )
              )
            )
            /\
            (
              (
                ( NTP4VCOffset tp1 )
                +
                ( NTP4VCSigned32 F )
              )
              <_
              ( NTP4VCMax tp1 )
            )
            /\
            ( NTP4VCAfterO5 tp1 B C D E F G H )
          )
        )
      )
  ) $.
$}

${
  $d qp A B C D E F G H $.

  ntp4vc-after-qp-definition $a |- (
    NTP4VCAfterQp A B C D E F G H
  ) <-> (
    A. qp e. ( NTP4VCPtr H )
      (
        ( NTP4VCAllocation qp G )
        ->
        (
          (
            ( NTP4VCValid A ( NTP4VCSigned32 E ) )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          ( NTP4VCAfterTp1 A B C qp D E F H )
        )
      )
  ) $.
$}

${
  $d o4 A B C D E F G H $.

  ntp4vc-after-o4-definition $a |- (
    NTP4VCAfterO4 A B C D E F G H
  ) <-> (
    A. o4 e. NTP4VCWord32
      (
        ( o4 = ( NTP4VCSigned32 G ) )
        ->
        (
          0 <_ o4
          /\
          ( NTP4VCAfterQp A B C D E F o4 H )
        )
      )
  ) $.
$}

${
  $d o3 A B C D E F G $.

  ntp4vc-after-o3-definition $a |- (
    NTP4VCAfterO3 A B C D E F G
  ) <-> (
    A. o3 e. NTP4VCWord32
      (
        (
          ( NTP4VCSigned32 o3 )
          =
          ( ( NTP4VCSigned32 F ) + 1 )
        )
        ->
        (
          0 <_ ( NTP4VCSigned32 o3 )
          /\
          ( NTP4VCAfterO4 A B C D E F o3 G )
        )
      )
  ) $.
$}

${
  $d tp A B C D E F G $.

  ntp4vc-after-tp-definition $a |- (
    NTP4VCAfterTp A B C D E F G
  ) <-> (
    A. tp e. ( NTP4VCPtr G )
      (
        ( NTP4VCAllocation tp F )
        ->
        (
          (
            NTP4VCInt32InBounds
              ( ( NTP4VCSigned32 E ) + 1 )
          )
          /\
          ( NTP4VCAfterO3 tp A B C D E G )
        )
      )
  ) $.
$}

${
  $d o2 A B C D E F G $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C D E F G
  ) <-> (
    A. o2 e. NTP4VCWord32
      (
        ( o2 = ( NTP4VCSigned32 F ) )
        ->
        (
          0 <_ o2
          /\
          ( NTP4VCAfterTp A B C D E o2 G )
        )
      )
  ) $.
$}

${
  $d o1 A B C D E F $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E F
  ) <-> (
    A. o1 e. NTP4VCWord32
      (
        (
          ( NTP4VCSigned32 o1 )
          =
          (
            ( NTP4VCSigned32 E )
            +
            ( NTP4VCSigned32 D )
          )
        )
        ->
        (
          0 <_ ( NTP4VCSigned32 o1 )
          /\
          ( NTP4VCAfterO2 A B C D E o1 F )
        )
      )
  ) $.
$}

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-rp-pointer $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-n-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-up-pointer $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-un-word32 $e |- D e. NTP4VCWord32 $.
  ntp4vc-mp-pointer $e |- E e. ( NTP4VCPtr Z ) $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- (
    NTP4VCValid C ( NTP4VCSigned32 D )
  ) $.
  ntp4vc-fact2 $e |- (
    NTP4VCValid E ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact3 $e |- 1 <_ ( NTP4VCSigned32 B ) $.
  ntp4vc-fact4 $e |- 1 <_ ( NTP4VCSigned32 D ) $.
  ntp4vc-fact5 $e |- (
    ( NTP4VCSigned32 D ) + ( NTP4VCSigned32 B )
  ) < ( ( 2 ^ ; 3 1 ) - 1 ) $.
  ntp4vc-fact6 $e |- 0 < (
    NTP4VCPelts E
      (
        (
          ( NTP4VCOffset E )
          +
          ( NTP4VCSigned32 B )
        )
        -
        1
      )
  ) $.
  ntp4vc-fact7 $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-pearl-multiprecision-powm-redcify-vc $a |- (
    (
      NTP4VCInt32InBounds
        (
          ( NTP4VCSigned32 D )
          +
          ( NTP4VCSigned32 B )
        )
    )
    /\
    ( NTP4VCAfterO1 C E A B D Z )
  ) $.
$}
