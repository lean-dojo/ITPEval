$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_otherqtvc: the
  verification condition for converting a positive multiprecision integer
  to digits in an arbitrary base, including quotient extraction, zero
  padding, final-limb conversion, reversal, and preservation of the memory
  frame. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Fixed-width words use their complete finite carriers. Signed 32-bit
  interpretation is two's complement; bytes and limbs retain the unsigned
  UChar and uint64 interpretations of the Why3 source. Pointers are exact
  tuples of a finite data sequence, offset, lower and upper bounds,
  writability bit, and a nonempty allocation zone. Lookup is totalized with
  Int.toNat. The phase predicates are definitional factorizations of the
  nested generated VC; proposition-valued conditionals are represented by
  their two guarded implications. The final declaration is an unproved
  Metamath $a statement, and there is no $p declaration.
$)

$c
  NTP4VCWord8 NTP4VCWord32 NTP4VCWord64
  NTP4VCSigned32 NTP4VCInt32InBounds NTP4VCUInt32InBounds
  NTP4VCToNat NTP4VCIPow
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCPelts
  NTP4VCValid NTP4VCAccess NTP4VCSameFrame NTP4VCShiftView
  NTP4VCUpdateLaw NTP4VCMapEqSubShift NTP4VCFrame
  NTP4VCValue NTP4VCInBase NTP4VCSValueLeSub NTP4VCSValueLe
  NTP4VCSValueSub NTP4VCSValue
  NTP4VCBaseInfo NTP4VCBase NTP4VCExp NTP4VCBigBase
  NTP4VCReciprocal
  NTP4VCConversionPre NTP4VCConversionPost
  NTP4VCPaddingInvariant NTP4VCPaddingStep
  NTP4VCDivisionInvariant NTP4VCDivisionStep
  NTP4VCReverseInvariant NTP4VCReverseStep
  NTP4VCFinalPost NTP4VCFinalLimb NTP4VCSingleLimb NTP4VCMultiLimb
  NTP4VCGetStrOtherVC
$.

ntp4vc-word8-syntax $a class NTP4VCWord8 $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syntax $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint32-bounds-syntax $a wff ( NTP4VCUInt32InBounds A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-ipow-syntax $a class ( NTP4VCIPow A B ) $.
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
ntp4vc-shift-view-syntax $a wff ( NTP4VCShiftView A B C ) $.
ntp4vc-update-law-syntax $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-map-eq-syntax $a wff ( NTP4VCMapEqSubShift A B C D E ) $.
ntp4vc-frame-syntax $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-in-base-syntax $a wff ( NTP4VCInBase A B C D ) $.
ntp4vc-svalue-le-sub-syntax $a class ( NTP4VCSValueLeSub A B C D ) $.
ntp4vc-svalue-le-syntax $a class ( NTP4VCSValueLe A B C ) $.
ntp4vc-svalue-sub-syntax $a class ( NTP4VCSValueSub A B C D ) $.
ntp4vc-svalue-syntax $a class ( NTP4VCSValue A B C ) $.
ntp4vc-base-info-syntax $a class NTP4VCBaseInfo $.
ntp4vc-base-syntax $a class ( NTP4VCBase A ) $.
ntp4vc-exp-syntax $a class ( NTP4VCExp A ) $.
ntp4vc-big-base-syntax $a class ( NTP4VCBigBase A ) $.
ntp4vc-reciprocal-syntax $a wff ( NTP4VCReciprocal A B ) $.
ntp4vc-conversion-pre-syntax
  $a wff ( NTP4VCConversionPre A B C D E F G H I ) $.
ntp4vc-conversion-post-syntax
  $a wff ( NTP4VCConversionPost A B C D E F G ) $.
ntp4vc-padding-invariant-syntax
  $a wff ( NTP4VCPaddingInvariant A B C D E F G H I J K ) $.
ntp4vc-padding-step-syntax
  $a wff ( NTP4VCPaddingStep A B C D E F G H I J K L M N ) $.
ntp4vc-division-invariant-syntax
  $a wff ( NTP4VCDivisionInvariant A B C D E F G H I J K L ) $.
ntp4vc-division-step-syntax
  $a wff ( NTP4VCDivisionStep A B C D E F G H I J K L M N O P ) $.
ntp4vc-reverse-invariant-syntax
  $a wff ( NTP4VCReverseInvariant A B C D E F G ) $.
ntp4vc-reverse-step-syntax
  $a wff ( NTP4VCReverseStep A B C D E F G H I J ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C D E F G ) $.
ntp4vc-final-limb-syntax
  $a wff ( NTP4VCFinalLimb A B C D E F G H I J K ) $.
ntp4vc-single-limb-syntax
  $a wff ( NTP4VCSingleLimb A B C D E F G H I J K ) $.
ntp4vc-multi-limb-syntax
  $a wff ( NTP4VCMultiLimb A B C D E F G H I J K ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCGetStrOtherVC A B C D E F G ) $.

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

ntp4vc-uint32-bounds-definition $a |- ( NTP4VCUInt32InBounds A ) <-> (
  A e. NTP4VCWord32
) $.

ntp4vc-to-nat-definition $a |- ( NTP4VCToNat A ) =
  if ( 0 <_ A , A , 0 ) $.

ntp4vc-ipow-definition $a |- ( NTP4VCIPow A B ) =
  ( A ^ ( NTP4VCToNat B ) ) $.

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

ntp4vc-shift-view-definition $a |- ( NTP4VCShiftView A B C ) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C ) /\
  ( ( # ` ( NTP4VCData A ) ) = ( # ` ( NTP4VCData B ) ) /\
    ( ( NTP4VCData A ) = ( NTP4VCData B ) /\
      ( ( NTP4VCMin A ) = ( NTP4VCMin B ) /\
        ( ( NTP4VCMax A ) = ( NTP4VCMax B ) /\
          ( ( NTP4VCZone A ) = ( NTP4VCZone B ) /\
            ( NTP4VCWritable A ) = ( NTP4VCWritable B ) ) ) ) ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $.
  ntp4vc-update-law-definition $a |- ( NTP4VCUpdateLaw A B C D ) <-> (
    A. x e. ZZ ( ( NTP4VCPelts A x ) =
      if ( x = C , D , ( NTP4VCPelts B x ) ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  ntp4vc-map-eq-definition $a |- ( NTP4VCMapEqSubShift A B C D E ) <-> (
    A. x e. ZZ ( ( 0 <_ x /\ x < E ) ->
      ( NTP4VCPelts A ( C + x ) ) = ( NTP4VCPelts B ( D + x ) ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $.
  ntp4vc-frame-definition $a |- ( NTP4VCFrame A B C ) <-> (
    A. x e. ZZ (
      ( x < ( NTP4VCOffset A ) \/
        ( ( NTP4VCOffset A ) + C ) <_ x ) ->
      ( NTP4VCPelts A x ) = ( NTP4VCPelts B x )
    )
  ) $.
$}

${
  $d x A $. $d x B $.
  ntp4vc-value-definition $a |- ( NTP4VCValue A B ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat B ) )
      ( ( NTP4VCPelts A ( ( NTP4VCOffset A ) + x ) )
        x. ( ( 2 ^ ; 6 4 ) ^ x ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $.
  ntp4vc-in-base-definition $a |- ( NTP4VCInBase A B C D ) <-> (
    A. x e. ZZ ( ( C <_ x /\ x < D ) ->
      ( 0 <_ ( NTP4VCPelts B x ) /\ ( NTP4VCPelts B x ) < A ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $.
  ntp4vc-svalue-le-sub-definition $a |- (
    NTP4VCSValueLeSub A B C D
  ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat ( D - C ) ) )
      ( ( A ^ x ) x. ( NTP4VCPelts B ( C + x ) ) )
  ) $.
$}

ntp4vc-svalue-le-definition $a |- ( NTP4VCSValueLe A B C ) = (
  NTP4VCSValueLeSub A B ( NTP4VCOffset B )
    ( ( NTP4VCOffset B ) + C )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $.
  ntp4vc-svalue-sub-definition $a |- ( NTP4VCSValueSub A B C D ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat ( D - C ) ) )
      ( ( A ^ ( ( ( NTP4VCToNat ( D - C ) ) - 1 ) - x ) )
        x. ( NTP4VCPelts B ( C + x ) ) )
  ) $.
$}

ntp4vc-svalue-definition $a |- ( NTP4VCSValue A B C ) = (
  NTP4VCSValueSub A B ( NTP4VCOffset B )
    ( ( NTP4VCOffset B ) + C )
) $.

ntp4vc-base-info-definition $a |- NTP4VCBaseInfo = {
  x e. ( ZZ X. ( NTP4VCWord32 X. NTP4VCWord64 ) )
  |
  (
    (
      2 <_ ( 1st ` x )
      /\
      ( 1st ` x ) <_ ; 2 5 6
    )
    /\
    (
      (
        7 <_ ( 1st ` ( 2nd ` x ) )
        /\
        ( 1st ` ( 2nd ` x ) ) <_ ; 6 3
      )
      /\
      (
        ( 2 ^ ; 6 4 )
        <_
        (
          ( 2nd ` ( 2nd ` x ) )
          x.
          ( 1st ` x )
        )
        /\
        (
          2nd ` ( 2nd ` x )
        )
        =
        (
          NTP4VCIPow
            ( 1st ` x )
            ( 1st ` ( 2nd ` x ) )
        )
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
  A = (
    ( |_ ` ( ( ( ( 2 ^ ; 6 4 ) x. ( 2 ^ ; 6 4 ) ) - 1 ) / B ) )
    - ( 2 ^ ; 6 4 )
  )
) $.

ntp4vc-conversion-pre-definition $a |- (
  NTP4VCConversionPre A B C D E F G H I
) <-> (
  ( ( 2 <_ ( NTP4VCBase C ) /\ ( NTP4VCBase C ) <_ ; 2 5 6 ) /\
    ( ( NTP4VCWritable D ) = 1 /\
      ( ( ( 2 ^ ; 6 4 ) / 2 ) <_ H /\
        ( ( 0 <_ G /\ G <_ ; 6 3 ) /\
          ( ( NTP4VCBase C ) x. ( 2 ^ G ) ) = H ) ) ) ) /\
  ( ( NTP4VCReciprocal I H ) /\
    ( ( NTP4VCValid D F /\ 0 < F ) /\
      A < ( ( NTP4VCBase C ) ^ F ) ) )
) $.

ntp4vc-conversion-post-definition $a |- (
  NTP4VCConversionPost A B C D E F G
) <-> (
  ( NTP4VCSValueLe ( NTP4VCBase C ) D G ) = A /\
  ( ( 0 <_ G /\ G <_ F ) /\
    ( ( 0 < G -> 0 < ( NTP4VCPelts D
        ( ( NTP4VCOffset D ) + G - 1 ) ) ) /\
      ( ( NTP4VCInBase ( NTP4VCBase C ) D
          ( NTP4VCOffset D ) ( ( NTP4VCOffset D ) + G ) ) /\
        ( NTP4VCFrame D E G ) ) ) )
) $.

ntp4vc-padding-invariant-definition $a |- (
  NTP4VCPaddingInvariant A B C D E F G H I J K
) <-> (
  ( G <_ ( NTP4VCExp C ) /\
    ( NTP4VCSigned32 H ) = ( ( NTP4VCSigned32 F ) + G ) ) /\
  ( ( NTP4VCInBase ( NTP4VCSigned32 B ) D
      ( NTP4VCOffset D )
      ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 H ) ) ) /\
    ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) D
          ( NTP4VCSigned32 H ) )
      + ( ( NTP4VCSigned32 B ) ^
          ( ( NTP4VCSigned32 H ) - G + ( NTP4VCExp C ) ) )
        x. ( NTP4VCValue E ( NTP4VCSigned32 I ) ) ) = A ) /\
  ( NTP4VCFrame D J ( NTP4VCSigned32 K ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  $d x F $. $d x G $. $d x H $. $d x I $. $d x J $.
  $d x K $. $d x L $. $d x M $. $d x N $.
  $d y A $. $d y B $. $d y C $. $d y D $. $d y E $.
  $d y F $. $d y G $. $d y H $. $d y I $. $d y J $.
  $d y K $. $d y L $. $d y M $. $d y N $.
  $d z A $. $d z B $. $d z C $. $d z D $. $d z E $.
  $d z F $. $d z G $. $d z H $. $d z I $. $d z J $.
  $d z K $. $d z L $. $d z M $. $d z N $.
  $d w A $. $d w B $. $d w C $. $d w D $. $d w E $.
  $d w F $. $d w G $. $d w H $. $d w I $. $d w J $.
  $d w K $. $d w L $. $d w M $. $d w N $.
  $d v A $. $d v B $. $d v C $. $d v D $. $d v E $.
  $d v F $. $d v G $. $d v H $. $d v I $. $d v J $.
  $d v K $. $d v L $. $d v M $. $d v N $.
  $d u A $. $d u B $. $d u C $. $d u D $. $d u E $.
  $d u F $. $d u G $. $d u H $. $d u I $. $d u J $.
  $d u K $. $d u L $. $d u M $. $d u N $.
  ntp4vc-padding-step-definition $a |- (
    NTP4VCPaddingStep A B C D E F G H I J K L M N
  ) <-> (
    A. x e. NTP4VCWord32 (
      A. y e. NTP4VCWord32 (
        A. z e. ( NTP4VCPtr NTP4VCWord8 N ) (
          ( NTP4VCSameFrame z D ) ->
          ( ( NTP4VCPaddingInvariant
                A B C z E F x y G K L ) ->
            ( ( x < ( NTP4VCExp C ) -> (
                ( NTP4VCAccess z ( NTP4VCSigned32 y ) /\
                  ( NTP4VCWritable z ) = 1 ) /\
                A. w e. ( NTP4VCPtr NTP4VCWord8 N ) (
                  ( ( NTP4VCSameFrame w z ) /\
                    ( NTP4VCUpdateLaw w z
                      ( ( NTP4VCOffset w ) +
                        ( NTP4VCSigned32 y ) ) 0 ) ) ->
                  ( ( NTP4VCInt32InBounds
                        ( ( NTP4VCSigned32 y ) + 1 ) ) /\
                    A. v e. NTP4VCWord32 (
                      ( ( NTP4VCSigned32 v ) =
                          ( ( NTP4VCSigned32 y ) + 1 ) ) ->
                      ( ( NTP4VCUInt32InBounds ( x + 1 ) ) /\
                        A. u e. NTP4VCWord32 (
                          ( u = ( x + 1 ) ) ->
                          ( ( 0 <_ ( ( NTP4VCExp C ) - x ) /\
                              ( ( NTP4VCExp C ) - u ) <
                                ( ( NTP4VCExp C ) - x ) ) /\
                            ( NTP4VCPaddingInvariant
                                A B C w E F u v G K L ) )
                        )
                      )
                    )
                  )
                )
              ) ) /\
              ( ( -. x < ( NTP4VCExp C ) ) -> (
                ( ( 0 <_ ( NTP4VCValue H
                              ( NTP4VCSigned32 I ) ) /\
                    ( NTP4VCValue E ( NTP4VCSigned32 G ) ) <
                      ( NTP4VCValue H ( NTP4VCSigned32 I ) ) ) /\
                  ( NTP4VCDivisionInvariant
                      A B C z E L G y M ( J + 1 ) K L ) )
              ) ) )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-division-invariant-definition $a |- (
  NTP4VCDivisionInvariant A B C D E F G H I J K L
) <-> (
  ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) D
        ( NTP4VCSigned32 H ) )
      + ( ( NTP4VCSigned32 B ) ^ ( NTP4VCSigned32 H ) )
        x. ( NTP4VCValue E ( NTP4VCSigned32 G ) ) ) = A /\
  ( ( 1 <_ ( NTP4VCSigned32 G ) /\
      ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 I ) ) /\
    ( ( ( NTP4VCSigned32 I ) - ( NTP4VCSigned32 G ) ) <_ J /\
      ( ( 0 <_ ( NTP4VCSigned32 H ) /\
          ( NTP4VCSigned32 H ) < ( NTP4VCSigned32 F ) ) /\
        ( ( NTP4VCSigned32 H ) = ( J x. ( NTP4VCExp C ) ) /\
          ( NTP4VCInBase ( NTP4VCSigned32 B ) D
            ( NTP4VCOffset D )
            ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 H ) ) ) ) ) ) /\
  ( 0 < ( NTP4VCPelts E
      ( ( NTP4VCOffset E ) + ( NTP4VCSigned32 G ) - 1 ) ) /\
    ( NTP4VCFrame D K ( NTP4VCSigned32 L ) ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  $d x F $. $d x G $. $d x H $. $d x I $. $d x J $.
  $d x K $. $d x L $. $d x M $. $d x N $. $d x O $.
  $d x P $.
  ntp4vc-division-step-definition $a |- (
    NTP4VCDivisionStep A B C D E F G H I J K L M N O P
  ) <-> (
    ( 1 < ( NTP4VCSigned32 G ) -> (
      ( ( NTP4VCValid E ( NTP4VCSigned32 G ) /\
          NTP4VCValid H ( NTP4VCSigned32 G ) ) /\
        ( ( NTP4VCWritable H ) = 1 /\
          ( 0 < ( NTP4VCSigned32 G ) /\
            0 < ( NTP4VCBigBase C ) ) ) ) /\
      A. x e. ( NTP4VCPtr NTP4VCWord64 P ) (
        ( NTP4VCSameFrame x H ) ->
        A. y e. NTP4VCWord64 (
          ( ( NTP4VCValue E ( NTP4VCSigned32 G ) ) =
              ( ( NTP4VCValue x ( NTP4VCSigned32 G ) )
                x. ( NTP4VCBigBase C ) ) + y /\
            y < ( NTP4VCBigBase C ) ) ->
          ( ( NTP4VCValid x ( NTP4VCSigned32 G ) /\
              NTP4VCValid E ( NTP4VCSigned32 G ) ) /\
            ( NTP4VCWritable E ) = 1 ) /\
          A. z e. ( NTP4VCPtr NTP4VCWord64 P ) (
            ( NTP4VCSameFrame z E ) ->
            ( ( NTP4VCMapEqSubShift z x
                  ( NTP4VCOffset z ) ( NTP4VCOffset x )
                  ( NTP4VCSigned32 G ) ) /\
              ( NTP4VCFrame z E ( NTP4VCSigned32 G ) ) ) ->
            ( ( NTP4VCInt32InBounds
                  ( ( NTP4VCSigned32 G ) - 1 ) ) /\
              A. w e. NTP4VCWord32 (
                ( ( NTP4VCSigned32 w ) =
                    ( ( NTP4VCSigned32 G ) - 1 ) ) ->
                ( ( NTP4VCAccess z ( NTP4VCSigned32 w ) ) /\
                  A. v e. { 0 , 1 } (
                    ( ( ( NTP4VCPelts z
                            ( ( NTP4VCOffset z ) +
                              ( NTP4VCSigned32 w ) ) ) = 0 ->
                          v = 1 ) /\
                      ( v = 1 ->
                        ( NTP4VCPelts z
                          ( ( NTP4VCOffset z ) +
                            ( NTP4VCSigned32 w ) ) ) = 0 ) ) ->
                    A. u e. NTP4VCWord32 (
                      ( ( v = 1 -> u = 1 ) /\
                        ( ( -. v = 1 ) -> u = 0 ) ) ->
                      ( ( NTP4VCInt32InBounds
                            ( ( NTP4VCSigned32 G ) -
                              ( NTP4VCSigned32 u ) ) ) /\
                        A. t e. NTP4VCWord32 (
                          ( ( NTP4VCSigned32 t ) =
                              ( ( NTP4VCSigned32 G ) -
                                ( NTP4VCSigned32 u ) ) ) ->
                          ( ( ( NTP4VCMin D ) <_
                                ( ( NTP4VCOffset D ) +
                                  ( NTP4VCSigned32 I ) ) /\
                              ( ( NTP4VCOffset D ) +
                                ( NTP4VCSigned32 I ) ) <_
                                ( NTP4VCMax D ) ) /\
                            A. s e. ( NTP4VCPtr NTP4VCWord8 P ) (
                              ( NTP4VCShiftView s D
                                  ( NTP4VCSigned32 I ) ) ->
                              A. r e. NTP4VCWord32 (
                                r = ( NTP4VCExp C ) ->
                                ( r <_ ; 2 1 4 7 4 8 3 6 4 7 /\
                                  A. q e. NTP4VCWord32 (
                                    ( ( NTP4VCSigned32 q ) = r ) ->
                                    ( ( NTP4VCInt32InBounds
                                          ( ( NTP4VCSigned32 q ) + 1 ) ) /\
                                      A. p e. NTP4VCWord32 (
                                        ( ( NTP4VCSigned32 p ) =
                                            ( ( NTP4VCSigned32 q ) + 1 ) ) ->
                                        ( ( NTP4VCConversionPre
                                              y B C s D
                                              ( NTP4VCSigned32 p )
                                              M N O ) /\
                                          A. o e.
                                            ( NTP4VCPtr NTP4VCWord8 P ) (
                                            A. n e.
                                              ( NTP4VCPtr NTP4VCWord8 P ) (
                                              (
                                                ( NTP4VCData o ) =
                                                  ( NTP4VCData n ) /\
                                                (
                                                  ( NTP4VCSameFrame o s ) /\
                                                  ( NTP4VCSameFrame n D )
                                                )
                                              ) ->
                                              A. m e. NTP4VCWord32 (
                                                ( NTP4VCConversionPost
                                                    y B C o s
                                                    ( NTP4VCSigned32 p )
                                                    m ) ->
                                                ( m <_
                                                    ; 2 1 4 7 4 8 3 6 4 7 /\
                                                  A. l e. NTP4VCWord32 (
                                                    (
                                                      ( NTP4VCSigned32 l ) = m
                                                    ) ->
                                                    (
                                                      (
                                                        NTP4VCInt32InBounds
                                                        (
                                                          ( NTP4VCSigned32 I )
                                                          +
                                                          ( NTP4VCSigned32 l )
                                                        )
                                                      ) /\
                                                      A. k e. NTP4VCWord32 (
                                                        (
                                                          ( NTP4VCSigned32 k )
                                                          =
                                                          (
                                                            ( NTP4VCSigned32 I )
                                                            +
                                                            (
                                                              NTP4VCSigned32 l
                                                            )
                                                          )
                                                        ) ->
                                                        (
                                                          (
                                                            NTP4VCPaddingInvariant
                                                            A B C n z I m k t
                                                            K F
                                                          ) /\
                                                          (
                                                            NTP4VCPaddingStep
                                                            A B C n z I t E G
                                                            J K F L P
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    ) ) /\
    ( ( -. 1 < ( NTP4VCSigned32 G ) ) ->
      ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) D
            ( NTP4VCSigned32 I ) )
          + ( ( NTP4VCSigned32 B ) ^ ( NTP4VCSigned32 I ) )
            x. ( NTP4VCValue E 1 ) = A ) /\
      ( ( NTP4VCInBase ( NTP4VCSigned32 B ) D
            ( NTP4VCOffset D )
            ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 I ) ) ) /\
        ( ( 0 <_ ( NTP4VCSigned32 I ) /\
            ( NTP4VCSigned32 I ) < ( NTP4VCSigned32 F ) ) /\
          ( 0 < ( NTP4VCValue E 1 ) /\
            ( NTP4VCFrame D K ( NTP4VCSigned32 F ) ) ) ) ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $.
  $d x E $. $d x F $. $d x G $.
  ntp4vc-reverse-invariant-definition $a |- (
    NTP4VCReverseInvariant A B C D E F G
  ) <-> (
    ( ( 0 <_ ( ( 2 x. ( NTP4VCSigned32 F ) ) + 1 ) /\
        ( ( 2 x. ( NTP4VCSigned32 F ) ) + 1 ) <_
          ( ( NTP4VCSigned32 E ) + 1 ) ) /\
      ( A. x e. ZZ (
          ( ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 F ) ) <_ x /\
            x < ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E )
              - ( NTP4VCSigned32 F ) ) ) ->
          ( NTP4VCPelts D x ) = ( NTP4VCPelts C x )
        ) /\
        ( NTP4VCInBase ( NTP4VCSigned32 B ) D
          ( NTP4VCOffset D )
          ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E ) ) ) ) ) /\
    ( ( NTP4VCSValueSub ( NTP4VCSigned32 B ) D
          ( NTP4VCOffset D )
          ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 F ) ) )
        =
        ( NTP4VCSValueLeSub ( NTP4VCSigned32 B ) C
          ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E )
            - ( NTP4VCSigned32 F ) )
          ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E ) ) ) /\
      ( ( NTP4VCSValueSub ( NTP4VCSigned32 B ) D
            ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E )
              - ( NTP4VCSigned32 F ) )
            ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E ) ) )
          =
          ( NTP4VCSValueLeSub ( NTP4VCSigned32 B ) C
            ( NTP4VCOffset D )
            ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 F ) ) ) /\
        ( ( NTP4VCSValueLeSub ( NTP4VCSigned32 B ) D
              ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 F ) )
              ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E )
                - ( NTP4VCSigned32 F ) ) )
            =
            ( NTP4VCSValueLeSub ( NTP4VCSigned32 B ) C
              ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 F ) )
              ( ( NTP4VCOffset D ) + ( NTP4VCSigned32 E )
                - ( NTP4VCSigned32 F ) ) ) /\
          ( ( 0 < ( NTP4VCSigned32 F ) ->
              0 < ( NTP4VCPelts D ( NTP4VCOffset D ) ) ) /\
            ( NTP4VCFrame D A G ) ) ) )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  $d x F $. $d x G $. $d x H $. $d x I $. $d x J $. $d x K $.
  $d x L $. $d y L $.
  ntp4vc-reverse-step-definition $a |- (
    NTP4VCReverseStep A B C D E F G H I J
  ) <-> (
    ( NTP4VCInt32InBounds
        ( 2 x. ( NTP4VCSigned32 F ) ) ) /\
    A. x e. NTP4VCWord32 (
      ( ( NTP4VCSigned32 x ) =
          ( 2 x. ( NTP4VCSigned32 F ) ) ) ->
      ( ( NTP4VCInt32InBounds
            ( ( NTP4VCSigned32 x ) + 1 ) ) /\
        A. y e. NTP4VCWord32 (
          ( ( NTP4VCSigned32 y ) =
              ( ( NTP4VCSigned32 x ) + 1 ) ) ->
          ( ( ( NTP4VCSigned32 y ) < ( NTP4VCSigned32 E ) -> (
              ( NTP4VCAccess D ( NTP4VCSigned32 F ) /\
                ( NTP4VCInt32InBounds
                    ( ( NTP4VCSigned32 E ) -
                      ( NTP4VCSigned32 F ) ) ) ) /\
              A. z e. NTP4VCWord32 (
                ( ( NTP4VCSigned32 z ) =
                    ( ( NTP4VCSigned32 E ) -
                      ( NTP4VCSigned32 F ) ) ) ->
                ( ( NTP4VCInt32InBounds
                      ( ( NTP4VCSigned32 z ) - 1 ) ) /\
                  A. w e. NTP4VCWord32 (
                    ( ( NTP4VCSigned32 w ) =
                        ( ( NTP4VCSigned32 z ) - 1 ) ) ->
                    ( ( NTP4VCAccess D ( NTP4VCSigned32 w ) ) /\
                      ( ( NTP4VCAccess D
                            ( NTP4VCSigned32 F ) /\
                          ( NTP4VCWritable D ) = 1 ) /\
                        A. v e. ( NTP4VCPtr NTP4VCWord8 J ) (
                          ( ( NTP4VCSameFrame v D ) /\
                            ( NTP4VCUpdateLaw v D
                              ( ( NTP4VCOffset v ) +
                                ( NTP4VCSigned32 F ) )
                              ( NTP4VCPelts D
                                ( ( NTP4VCOffset D ) +
                                  ( NTP4VCSigned32 w ) ) ) ) ) ->
                          ( ( NTP4VCInt32InBounds
                                ( ( NTP4VCSigned32 E ) -
                                  ( NTP4VCSigned32 F ) ) ) /\
                            A. u e. NTP4VCWord32 (
                              ( ( NTP4VCSigned32 u ) =
                                  ( ( NTP4VCSigned32 E ) -
                                    ( NTP4VCSigned32 F ) ) ) ->
                              ( ( NTP4VCInt32InBounds
                                    ( ( NTP4VCSigned32 u ) - 1 ) ) /\
                                A. t e. NTP4VCWord32 (
                                  ( ( NTP4VCSigned32 t ) =
                                      ( ( NTP4VCSigned32 u ) - 1 ) ) ->
                                  ( ( NTP4VCAccess v
                                        ( NTP4VCSigned32 t ) /\
                                      ( NTP4VCWritable v ) = 1 ) /\
                                    A. s e.
                                      ( NTP4VCPtr NTP4VCWord8 J ) (
                                      ( ( NTP4VCSameFrame s v ) /\
                                        ( NTP4VCUpdateLaw s v
                                          ( ( NTP4VCOffset s ) +
                                            ( NTP4VCSigned32 t ) )
                                          ( NTP4VCPelts D
                                            ( ( NTP4VCOffset D ) +
                                              ( NTP4VCSigned32 F ) ) ) ) ) ->
                                      ( ( NTP4VCInt32InBounds
                                            (
                                              ( NTP4VCSigned32 F ) + 1
                                            ) ) /\
                                        A. r e. NTP4VCWord32 (
                                          (
                                            ( NTP4VCSigned32 r ) =
                                            (
                                              ( NTP4VCSigned32 F ) + 1
                                            )
                                          ) ->
                                          (
                                            (
                                              0 <_
                                                (
                                                  ( NTP4VCSigned32 E ) -
                                                  ( NTP4VCSigned32 F )
                                                ) /\
                                              (
                                                ( NTP4VCSigned32 E ) -
                                                ( NTP4VCSigned32 r )
                                              ) <
                                              (
                                                ( NTP4VCSigned32 E ) -
                                                ( NTP4VCSigned32 F )
                                              )
                                            ) /\
                                            (
                                              NTP4VCReverseInvariant
                                              A B C s E r G
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            ) ) /\
            ( ( -. ( NTP4VCSigned32 y ) <
                    ( NTP4VCSigned32 E ) ) ->
              ( 0 <_ ( NTP4VCSigned32 E ) /\
                A. q e. NTP4VCWord32 (
                  ( q = ( NTP4VCSigned32 E ) ) ->
                  ( NTP4VCFinalPost A B H D q G I )
                ) )
            ) )
        )
      )
    )
  ) $.
$}

ntp4vc-final-post-definition $a |- (
  NTP4VCFinalPost A B C D E F G
) <-> (
  ( 0 <_ E /\ E < ( NTP4VCSigned32 F ) ) /\
  ( ( NTP4VCSValue ( NTP4VCSigned32 B ) D
        E ) =
      ( NTP4VCValue C ( NTP4VCSigned32 G ) ) /\
    ( ( NTP4VCInBase ( NTP4VCSigned32 B ) D
        ( NTP4VCOffset D )
        ( ( NTP4VCOffset D ) + E ) ) /\
      ( 0 < ( NTP4VCPelts D ( NTP4VCOffset D ) ) /\
        ( NTP4VCFrame D A ( NTP4VCSigned32 F ) ) ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  $d x F $. $d x G $. $d x H $. $d x I $. $d x J $. $d x K $.
  $d y A $. $d y B $. $d y C $. $d y D $. $d y E $.
  $d y F $. $d y G $. $d y H $. $d y I $. $d y J $. $d y K $.
  $d z A $. $d z B $. $d z C $. $d z D $. $d z E $.
  $d z F $. $d z G $. $d z H $. $d z I $. $d z J $. $d z K $.
  $d w A $. $d w B $. $d w C $. $d w D $. $d w E $.
  $d w F $. $d w G $. $d w H $. $d w I $. $d w J $. $d w K $.
  $d v A $. $d v B $. $d v C $. $d v D $. $d v E $.
  $d v F $. $d v G $. $d v H $. $d v I $. $d v J $. $d v K $.
  $d u A $. $d u B $. $d u C $. $d u D $. $d u E $.
  $d u F $. $d u G $. $d u H $. $d u I $. $d u J $. $d u K $.
  $d t A $. $d t B $. $d t C $. $d t D $. $d t E $.
  $d t F $. $d t G $. $d t H $. $d t I $. $d t J $. $d t K $.
  $d s A $. $d s B $. $d s C $. $d s D $. $d s E $.
  $d s F $. $d s G $. $d s H $. $d s I $. $d s J $. $d s K $.
  $d r A $. $d r B $. $d r C $. $d r D $. $d r E $.
  $d r F $. $d r G $. $d r H $. $d r I $. $d r J $. $d r K $.
  ntp4vc-final-limb-definition $a |- (
    NTP4VCFinalLimb A B C D E F G H I J K
  ) <-> (
    A. x e. NTP4VCWord32 (
      A. y e. ( NTP4VCPtr NTP4VCWord64 K ) (
        ( NTP4VCSameFrame y C ) ->
        A. z e. ( NTP4VCPtr NTP4VCWord8 K ) (
          ( NTP4VCSameFrame z E ) ->
          ( ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) z
                    ( NTP4VCSigned32 x ) )
                + ( ( NTP4VCSigned32 B ) ^
                    ( NTP4VCSigned32 x ) )
                  x. ( NTP4VCValue y 1 ) = A ) /\
            ( ( NTP4VCInBase ( NTP4VCSigned32 B ) z
                  ( NTP4VCOffset z )
                  ( ( NTP4VCOffset z ) +
                    ( NTP4VCSigned32 x ) ) ) /\
              ( ( 0 <_ ( NTP4VCSigned32 x ) /\
                  ( NTP4VCSigned32 x ) <
                    ( NTP4VCSigned32 G ) ) /\
                ( 0 < ( NTP4VCValue y 1 ) /\
                  ( NTP4VCFrame z E
                    ( NTP4VCSigned32 G ) ) ) ) ) ) ->
          ( ( NTP4VCAccess y 0 ) /\
            ( ( ( NTP4VCMin z ) <_
                  ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 x ) ) /\
                ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 x ) ) <_
                  ( NTP4VCMax z ) ) /\
              A. w e. ( NTP4VCPtr NTP4VCWord8 K ) (
                ( NTP4VCShiftView w z ( NTP4VCSigned32 x ) ) ->
                ( ( NTP4VCInt32InBounds
                      ( ( NTP4VCSigned32 G ) - 1 ) ) /\
                  A. v e. NTP4VCWord32 (
                    ( ( NTP4VCSigned32 v ) =
                        ( ( NTP4VCSigned32 G ) - 1 ) ) ->
                    ( ( NTP4VCInt32InBounds
                          ( ( NTP4VCSigned32 v ) -
                            ( NTP4VCSigned32 x ) ) ) /\
                      A. u e. NTP4VCWord32 (
                        ( ( NTP4VCSigned32 u ) =
                            ( ( NTP4VCSigned32 v ) -
                              ( NTP4VCSigned32 x ) ) ) ->
                        ( ( NTP4VCConversionPre
                              ( NTP4VCPelts y ( NTP4VCOffset y ) )
                              B F w z ( NTP4VCSigned32 u )
                              H I J ) /\
                          A. t e. ( NTP4VCPtr NTP4VCWord8 K ) (
                            A. s e. ( NTP4VCPtr NTP4VCWord8 K ) (
                              ( ( NTP4VCData t ) = ( NTP4VCData s ) /\
                                ( ( NTP4VCSameFrame t w ) /\
                                  ( NTP4VCSameFrame s z ) ) ) ->
                              A. r e. NTP4VCWord32 (
                                ( NTP4VCConversionPost
                                    ( NTP4VCPelts y
                                      ( NTP4VCOffset y ) )
                                    B F t w ( NTP4VCSigned32 u )
                                    r ) ->
                                ( r <_ ; 2 1 4 7 4 8 3 6 4 7 /\
                                  A. q e. NTP4VCWord32 (
                                    ( ( NTP4VCSigned32 q ) = r ) ->
                                    ( ( NTP4VCInt32InBounds
                                          ( ( NTP4VCSigned32 x ) +
                                            ( NTP4VCSigned32 q ) ) ) /\
                                      A. p e. NTP4VCWord32 (
                                        ( ( NTP4VCSigned32 p ) =
                                            ( ( NTP4VCSigned32 x ) +
                                              ( NTP4VCSigned32 q ) ) ) ->
                                        ( ( NTP4VCReverseInvariant
                                              E B s s p 0 G ) /\
                                          A. o e. NTP4VCWord32 (
                                            A. n e.
                                              ( NTP4VCPtr
                                                NTP4VCWord8 K ) (
                                              ( NTP4VCSameFrame n s ) ->
                                              ( ( NTP4VCReverseInvariant
                                                    E B s n p o G ) ->
                                                ( NTP4VCReverseStep
                                                    E B s n p o G
                                                    C D K ) )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-single-limb-definition $a |- (
  NTP4VCSingleLimb A B C D E F G H I J K
) <-> (
  ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) E 0 )
      + ( ( NTP4VCSigned32 B ) ^ 0 ) x. ( NTP4VCValue C 1 ) = A ) /\
  ( ( NTP4VCInBase ( NTP4VCSigned32 B ) E
        ( NTP4VCOffset E ) ( NTP4VCOffset E ) ) /\
    ( ( 0 <_ 0 /\ 0 < ( NTP4VCSigned32 G ) ) /\
      ( 0 < ( NTP4VCValue C 1 ) ) ) )
) $.

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $.
  $d x F $. $d x G $. $d x H $. $d x I $. $d x J $. $d x K $.
  $d y A $. $d y B $. $d y C $. $d y D $. $d y E $.
  $d y F $. $d y G $. $d y H $. $d y I $. $d y J $. $d y K $.
  $d z A $. $d z B $. $d z C $. $d z D $. $d z E $.
  $d z F $. $d z G $. $d z H $. $d z I $. $d z J $. $d z K $.
  $d w A $. $d w B $. $d w C $. $d w D $. $d w E $.
  $d w F $. $d w G $. $d w H $. $d w I $. $d w J $. $d w K $.
  $d v A $. $d v B $. $d v C $. $d v D $. $d v E $.
  $d v F $. $d v G $. $d v H $. $d v I $. $d v J $. $d v K $.
  $d u A $. $d u B $. $d u C $. $d u D $. $d u E $.
  $d u F $. $d u G $. $d u H $. $d u I $. $d u J $. $d u K $.
  $d t A $. $d t B $. $d t C $. $d t D $. $d t E $.
  $d t F $. $d t G $. $d t H $. $d t I $. $d t J $. $d t K $.
  $d s A $. $d s B $. $d s C $. $d s D $. $d s E $.
  $d s F $. $d s G $. $d s H $. $d s I $. $d s J $. $d s K $.
  ntp4vc-multi-limb-definition $a |- (
    NTP4VCMultiLimb A B C D E F G H I J K
  ) <-> (
    0 <_ ( NTP4VCSigned32 D ) /\
    A. x e. NTP4VCWord32 (
      x = ( NTP4VCSigned32 D ) ->
      ( 0 <_ x /\
        A. y e. ( NTP4VCPtr NTP4VCWord64 K ) (
          ( ( # ` ( NTP4VCData y ) ) = x /\
            ( ( NTP4VCOffset y ) = 0 /\ ( NTP4VCMin y ) = 0 ) /\
            ( ( NTP4VCMax y ) = x /\ ( NTP4VCWritable y ) = 1 ) ) ->
          ( ( ( NTP4VCSValueLe ( NTP4VCSigned32 B ) E 0 )
                + ( ( NTP4VCSigned32 B ) ^ 0 )
                  x. ( NTP4VCValue C ( NTP4VCSigned32 D ) ) = A ) /\
            ( NTP4VCDivisionInvariant
                A B F E C G D 0 D 0 E G ) ) /\
          A. z e. ZZ (
            A. w e. ( NTP4VCPtr NTP4VCWord64 K ) (
              ( NTP4VCSameFrame w y ) ->
              A. v e. NTP4VCWord32 (
                A. u e. NTP4VCWord32 (
                  A. t e. ( NTP4VCPtr NTP4VCWord64 K ) (
                    ( NTP4VCSameFrame t C ) ->
                    A. s e. ( NTP4VCPtr NTP4VCWord8 K ) (
                      ( NTP4VCSameFrame s E ) ->
                      ( NTP4VCDivisionInvariant
                          A B F s t G v u D z E G ) ->
                      ( NTP4VCDivisionStep
                          A B F s t G v w u z E D
                          H I J K )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $. $d x F $.
  $d x G $.
  ntp4vc-main-definition $a |- (
    NTP4VCGetStrOtherVC A B C D E F G
  ) <-> (
    0 <_ ( NTP4VCSigned32 D ) /\
    A. x e. NTP4VCWord64 (
      x = ( NTP4VCSigned32 D ) ->
      ( 0 < x /\
        A. y e. NTP4VCWord32 (
          ( ( ( 2 ^ ( NTP4VCSigned32 y ) ) x. x ) <_
                ( ( 2 ^ ; 6 4 ) - 1 ) /\
            ( ( ( 2 ^ ; 6 4 ) - 1 ) <
                ( 2 x. ( 2 ^ ( NTP4VCSigned32 y ) ) x. x ) /\
              ( 0 <_ ( NTP4VCSigned32 y ) /\
                ( NTP4VCSigned32 y ) < ; 6 4 ) ) ) ->
          A. z e. NTP4VCWord64 (
            z = ( NTP4VCSigned32 y ) ->
            ( 0 <_ ( NTP4VCSigned32 D ) /\
              A. w e. NTP4VCWord64 (
                w = ( NTP4VCSigned32 D ) ->
                ( ( ( 0 <_ z /\ z < ; 6 4 ) /\
                    ( ( 2 ^ z ) x. w ) <_
                      ( ( 2 ^ ; 6 4 ) - 1 ) ) /\
                  A. v e. NTP4VCWord64 (
                    v = ( ( 2 ^ z ) x. w ) ->
                    ( ( ( 2 ^ ; 6 4 ) / 2 ) <_ v /\
                      A. u e. NTP4VCWord64 (
                        ( NTP4VCReciprocal u v ) ->
                        ( ( ( 1 < ( NTP4VCSigned32 B ) ->
                            ( NTP4VCMultiLimb
                              ( NTP4VCValue A
                                ( NTP4VCSigned32 B ) )
                              D A B E C F z v u G ) ) /\
                          ( ( -. 1 < ( NTP4VCSigned32 B ) ) ->
                            ( NTP4VCSingleLimb
                              ( NTP4VCValue A
                                ( NTP4VCSigned32 B ) )
                              D A B E C F z v u G ) ) ) /\
                          ( NTP4VCFinalLimb
                            ( NTP4VCValue A
                              ( NTP4VCSigned32 B ) )
                            D A B E C F z v u G ) )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d Z U $. $d Z N $. $d Z I $. $d Z B $. $d Z S $. $d Z T $.

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-up-type $e |- U e. ( NTP4VCPtr NTP4VCWord64 Z ) $.
  ntp4vc-un-type $e |- N e. NTP4VCWord32 $.
  ntp4vc-info-type $e |- I e. NTP4VCBaseInfo $.
  ntp4vc-base-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-sp-type $e |- S e. ( NTP4VCPtr NTP4VCWord8 Z ) $.
  ntp4vc-sz-type $e |- T e. NTP4VCWord32 $.

  ntp4vc-up-valid $e |- ( NTP4VCValid U ( NTP4VCSigned32 N ) ) $.
  ntp4vc-un-positive $e |- 1 <_ ( NTP4VCSigned32 N ) $.
  ntp4vc-base-agrees $e |- ( NTP4VCBase I ) = ( NTP4VCSigned32 B ) $.
  ntp4vc-up-writable $e |- ( NTP4VCWritable U ) = 1 $.
  ntp4vc-sp-writable $e |- ( NTP4VCWritable S ) = 1 $.
  ntp4vc-top-positive $e |- 0 < ( NTP4VCPelts U
    ( ( NTP4VCOffset U ) + ( NTP4VCSigned32 N ) - 1 ) ) $.
  ntp4vc-sz-positive $e |- 0 < ( NTP4VCSigned32 T ) $.
  ntp4vc-sp-valid $e |- ( NTP4VCValid S ( NTP4VCSigned32 T ) ) $.
  ntp4vc-value-fits $e |- ( NTP4VCValue U ( NTP4VCSigned32 N ) ) <
    ( ( NTP4VCSigned32 B ) ^ ( ( NTP4VCSigned32 T ) - 1 ) ) $.

  ntp4vc-get-str-other-statement $a |- (
    NTP4VCGetStrOtherVC U N I B S T Z
  ) $.
$}
