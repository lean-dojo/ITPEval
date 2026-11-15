$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_strqtvc: the call-site
  verification condition for converting a positive multiprecision integer
  into base digits through either the power-of-two conversion or the
  general-base conversion. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Fixed-width words are represented by their complete unsigned integer
  carriers. NTP4VCSigned32 is the exact two's-complement interpretation of a
  32-bit word, while all source mathematical integers remain in SetMM's full
  unbounded integer class ZZ.

  A pointer is represented by its finite word-valued data sequence, integer
  offset and bounds, Boolean writability field, and an element of the
  arbitrary nonempty zone carrier Z. NTP4VCValid, NTP4VCValue,
  NTP4VCInBase, NTP4VCSValue, and NTP4VCFrame are definitional renderings of
  the corresponding Why3 predicates. NTP4VCBaseInfo is the exact record
  carrier satisfying the source type invariant.

  The remaining predicates factor the original nested verification
  condition without changing quantifier scope. Proposition-valued
  conditionals are expanded into their two exhaustive guarded implications.
  The final declaration is Metamath's native unproved $a statement encoding;
  every preceding $a is syntax or a faithful definition, and this database
  contains no $p proof declaration.
$)

$c
  NTP4VCWord8 NTP4VCWord32 NTP4VCWord64
  NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCToNat NTP4VCIPow NTP4VCEDiv
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCPelts NTP4VCValid
  NTP4VCSameFrame NTP4VCValue NTP4VCInBase
  NTP4VCSValueSub NTP4VCSValue NTP4VCFrame
  NTP4VCBaseInfo NTP4VCBase NTP4VCExp NTP4VCBigBase
  NTP4VCFinalPost NTP4VCBitsPremise NTP4VCBitsResults
  NTP4VCBitsPointers NTP4VCBitsCall NTP4VCBitsOutputs
  NTP4VCPowerBranch NTP4VCOtherPremise NTP4VCOtherResults
  NTP4VCOtherPointers NTP4VCOtherCall NTP4VCOtherInfos
  NTP4VCOtherOutputs NTP4VCGeneralBranch NTP4VCNotPowerTwo
  NTP4VCBitsContract NTP4VCAllBits NTP4VCAllBases
$.

ntp4vc-word8-syntax $a class NTP4VCWord8 $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
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
ntp4vc-same-frame-syntax
  $a wff ( NTP4VCSameFrame A B ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-in-base-syntax
  $a wff ( NTP4VCInBase A B C D ) $.
ntp4vc-svalue-sub-syntax
  $a class ( NTP4VCSValueSub A B C D ) $.
ntp4vc-svalue-syntax
  $a class ( NTP4VCSValue A B C ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-base-info-syntax $a class NTP4VCBaseInfo $.
ntp4vc-base-syntax $a class ( NTP4VCBase A ) $.
ntp4vc-exp-syntax $a class ( NTP4VCExp A ) $.
ntp4vc-big-base-syntax $a class ( NTP4VCBigBase A ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C D E F ) $.
ntp4vc-bits-premise-syntax
  $a wff ( NTP4VCBitsPremise A B C D E F G ) $.
ntp4vc-bits-results-syntax
  $a wff ( NTP4VCBitsResults A B C D E F G H ) $.
ntp4vc-bits-pointers-syntax
  $a wff ( NTP4VCBitsPointers A B C D E F G H ) $.
ntp4vc-bits-call-syntax
  $a wff ( NTP4VCBitsCall A B C D E F G H ) $.
ntp4vc-bits-outputs-syntax
  $a wff ( NTP4VCBitsOutputs A B C D E F G ) $.
ntp4vc-power-branch-syntax
  $a wff ( NTP4VCPowerBranch A B C D E F G ) $.
ntp4vc-other-premise-syntax
  $a wff ( NTP4VCOtherPremise A B C D E F G ) $.
ntp4vc-other-results-syntax
  $a wff ( NTP4VCOtherResults A B C D E F ) $.
ntp4vc-other-pointers-syntax
  $a wff ( NTP4VCOtherPointers A B C D E F ) $.
ntp4vc-other-call-syntax
  $a wff ( NTP4VCOtherCall A B C D E F G ) $.
ntp4vc-other-infos-syntax
  $a wff ( NTP4VCOtherInfos A B C D E F G ) $.
ntp4vc-other-outputs-syntax
  $a wff ( NTP4VCOtherOutputs A B C D E F ) $.
ntp4vc-general-branch-syntax
  $a wff ( NTP4VCGeneralBranch A B C D E F ) $.
ntp4vc-not-power-two-syntax
  $a wff ( NTP4VCNotPowerTwo A ) $.
ntp4vc-bits-contract-syntax
  $a wff ( NTP4VCBitsContract A B ) $.
ntp4vc-all-bits-syntax
  $a wff ( NTP4VCAllBits A B C D E F G ) $.
ntp4vc-all-bases-syntax
  $a wff ( NTP4VCAllBases A B C D E F ) $.

ntp4vc-word8-definition $a |- NTP4VCWord8 =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

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

ntp4vc-int32-bounds-definition $a |- (
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

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-ipow-definition $a |- (
  NTP4VCIPow A B
) = (
  A ^ ( NTP4VCToNat B )
) $.

ntp4vc-ediv-definition $a |- (
  NTP4VCEDiv A B
) = (
  |_ ` ( A / B )
) $.

ntp4vc-ptr-definition $a |- (
  NTP4VCPtr A B
) = (
  ( Word A )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. B ) ) ) )
) $.

ntp4vc-data-definition $a |- (
  NTP4VCData A
) = (
  1st ` A
) $.

ntp4vc-offset-definition $a |- (
  NTP4VCOffset A
) = (
  1st ` ( 2nd ` A )
) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A
) = (
  1st ` ( 2nd ` ( 2nd ` A ) )
) $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A
) = (
  1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
) $.

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

ntp4vc-pelts-definition $a |- (
  NTP4VCPelts A B
) = if (
  ( NTP4VCToNat B ) < ( # ` ( NTP4VCData A ) ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

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
        (
          ( NTP4VCOffset A ) + B
        ) <_ ( NTP4VCMax A )
        /\
        ( NTP4VCMax A ) <_ ( # ` ( NTP4VCData A ) )
      )
    )
  )
) $.

ntp4vc-same-frame-definition $a |- (
  NTP4VCSameFrame A B
) <-> (
  (
    ( # ` ( NTP4VCData A ) )
    =
    ( # ` ( NTP4VCData B ) )
  )
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
  $d x A $.  $d x B $.

  ntp4vc-value-definition $a |- (
    NTP4VCValue A B
  ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat B ) )
      (
        ( NTP4VCPelts A ( ( NTP4VCOffset A ) + x ) )
        x.
        ( ( 2 ^ ; 6 4 ) ^ x )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.

  ntp4vc-in-base-definition $a |- (
    NTP4VCInBase A B C D
  ) <-> (
    A. x e. ZZ
      (
        (
          C <_ x
          /\
          x < D
        )
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
  $d x A $.  $d x B $.  $d x C $.  $d x D $.

  ntp4vc-svalue-sub-definition $a |- (
    NTP4VCSValueSub A B C D
  ) = (
    sum_ x e. ( 0 ..^ ( NTP4VCToNat ( D - C ) ) )
      (
        (
          A
          ^
          (
            (
              ( NTP4VCToNat ( D - C ) )
              -
              1
            )
            -
            x
          )
        )
        x.
        ( NTP4VCPelts B ( C + x ) )
      )
  ) $.
$}

ntp4vc-svalue-definition $a |- (
  NTP4VCSValue A B C
) = (
  NTP4VCSValueSub A B
    ( NTP4VCOffset B )
    ( ( NTP4VCOffset B ) + C )
) $.

${
  $d x A $.  $d x B $.  $d x C $.

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
        (
          ( NTP4VCPelts A x )
          =
          ( NTP4VCPelts B x )
        )
      )
  ) $.
$}

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

ntp4vc-base-definition $a |- (
  NTP4VCBase A
) = (
  1st ` A
) $.

ntp4vc-exp-definition $a |- (
  NTP4VCExp A
) = (
  1st ` ( 2nd ` A )
) $.

ntp4vc-big-base-definition $a |- (
  NTP4VCBigBase A
) = (
  2nd ` ( 2nd ` A )
) $.

ntp4vc-final-post-definition $a |- (
  NTP4VCFinalPost A B C D E F
) <-> (
  (
    NTP4VCInBase A D
      ( NTP4VCOffset D )
      ( ( NTP4VCOffset D ) + F )
  )
  /\
  (
    ( NTP4VCSValue A D F )
    =
    ( NTP4VCValue B C )
  )
  /\
  (
    (
      0 < F
      /\
      F < E
    )
    /\
    0 < ( NTP4VCPelts D ( NTP4VCOffset D ) )
  )
) $.

ntp4vc-bits-premise-definition $a |- (
  NTP4VCBitsPremise A B C D E F G
) <-> (
  (
    NTP4VCInBase A E
      ( NTP4VCOffset E )
      ( ( NTP4VCOffset E ) + G )
  )
  /\
  (
    ( NTP4VCSValue A E G )
    =
    ( NTP4VCValue B C )
  )
  /\
  (
    (
      0 < G
      /\
      G <_ F
    )
    /\
    (
      0 < ( NTP4VCPelts E ( NTP4VCOffset E ) )
      /\
      ( NTP4VCFrame E D F )
    )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.

  ntp4vc-bits-results-definition $a |- (
    NTP4VCBitsResults A B C D E F G H
  ) <-> (
    A. x e. NTP4VCWord32
      (
        ( NTP4VCBitsPremise F B C D H G x )
        ->
        ( NTP4VCFinalPost A B C H E x )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.

  ntp4vc-bits-pointers-definition $a |- (
    NTP4VCBitsPointers A B C D E F G H
  ) <-> (
    A. x e. ( NTP4VCPtr NTP4VCWord8 H )
      (
        ( NTP4VCSameFrame x D )
        ->
        ( NTP4VCBitsResults A B C D E F G x )
      )
  ) $.
$}

ntp4vc-bits-call-definition $a |- (
  NTP4VCBitsCall A B C D E F G H
) <-> (
  (
    1 <_ C
    /\
    ( NTP4VCValid B C )
  )
  /\
  (
    (
      1 <_ F
      /\
      F <_ 8
    )
    /\
    (
      NTP4VCValid D
        (
          NTP4VCEDiv
            ( ( G + F ) - 1 )
            F
        )
    )
  )
  /\
  (
    (
      0 <_ G
      /\
      (
        NTP4VCValue B C
      ) < (
        NTP4VCIPow 2 G
      )
    )
    /\
    (
      0 < (
        NTP4VCPelts B
          ( ( ( NTP4VCOffset B ) + C ) - 1 )
      )
      /\
      (
        ( ( ; 6 4 x. C ) + 7 )
        <_
        ( ( 2 ^ ; 3 1 ) - 1 )
      )
    )
  )
  /\
  (
    ( NTP4VCWritable D ) = 1
    /\
    (
      NTP4VCBitsPointers A B C D E
        ( NTP4VCIPow 2 F )
        ( NTP4VCEDiv ( ( G + F ) - 1 ) F )
        H
    )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.

  ntp4vc-bits-outputs-definition $a |- (
    NTP4VCBitsOutputs A B C D E F G
  ) <-> (
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ; 6 4 x. C )
        ->
        (
          NTP4VCBitsCall A B C D E F
            ( NTP4VCSigned32 x ) G
        )
      )
  ) $.
$}

ntp4vc-power-branch-definition $a |- (
  NTP4VCPowerBranch A B C D E F G
) <-> (
  (
    NTP4VCInt32InBounds
      ( ; 6 4 x. C )
  )
  /\
  ( NTP4VCBitsOutputs A B C D E F G )
) $.

ntp4vc-other-premise-definition $a |- (
  NTP4VCOtherPremise A B C D E F G
) <-> (
  (
    0 <_ G
    /\
    G < E
  )
  /\
  (
    ( NTP4VCSValue A F G )
    =
    ( NTP4VCValue B C )
  )
  /\
  (
    NTP4VCInBase A F
      ( NTP4VCOffset F )
      ( ( NTP4VCOffset F ) + G )
  )
  /\
  (
    0 < ( NTP4VCPelts F ( NTP4VCOffset F ) )
    /\
    ( NTP4VCFrame F D E )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.

  ntp4vc-other-results-definition $a |- (
    NTP4VCOtherResults A B C D E F
  ) <-> (
    A. x e. NTP4VCWord32
      (
        ( NTP4VCOtherPremise A B C D E F x )
        ->
        ( NTP4VCFinalPost A B C F E x )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.

  ntp4vc-other-pointers-definition $a |- (
    NTP4VCOtherPointers A B C D E F
  ) <-> (
    A. x e. ( NTP4VCPtr NTP4VCWord8 F )
      (
        ( NTP4VCSameFrame x D )
        ->
        ( NTP4VCOtherResults A B C D E x )
      )
  ) $.
$}

ntp4vc-other-call-definition $a |- (
  NTP4VCOtherCall A B C D E F G
) <-> (
  (
    ( NTP4VCValid B C )
    /\
    1 <_ C
  )
  /\
  (
    ( NTP4VCBase F ) = A
    /\
    (
      ( NTP4VCWritable B ) = 1
      /\
      ( NTP4VCWritable D ) = 1
    )
  )
  /\
  (
    0 < (
      NTP4VCPelts B
        ( ( ( NTP4VCOffset B ) + C ) - 1 )
    )
    /\
    (
      0 < E
      /\
      ( NTP4VCValid D E )
    )
  )
  /\
  (
    (
      NTP4VCValue B C
    ) < (
      NTP4VCIPow A ( E - 1 )
    )
    /\
    ( NTP4VCOtherPointers A B C D E G )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.

  ntp4vc-other-infos-definition $a |- (
    NTP4VCOtherInfos A B C D E F G
  ) <-> (
    A. x e. NTP4VCBaseInfo
      (
        ( NTP4VCBase x ) = F
        ->
        ( NTP4VCOtherCall A B C D E x G )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.

  ntp4vc-other-outputs-definition $a |- (
    NTP4VCOtherOutputs A B C D E F
  ) <-> (
    A. x e. NTP4VCWord64
      (
        x = A
        ->
        (
          (
            2 <_ x
            /\
            x <_ ; 2 5 6
          )
          /\
          ( NTP4VCOtherInfos A B C D E x F )
        )
      )
  ) $.
$}

ntp4vc-general-branch-definition $a |- (
  NTP4VCGeneralBranch A B C D E F
) <-> (
  0 <_ A
  /\
  ( NTP4VCOtherOutputs A B C D E F )
) $.

${
  $d x A $.

  ntp4vc-not-power-two-definition $a |- (
    NTP4VCNotPowerTwo A
  ) <-> (
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          NTP4VCIPow 2 x
        ) =/= A
      )
  ) $.
$}

ntp4vc-bits-contract-definition $a |- (
  NTP4VCBitsContract A B
) <-> (
  (
    0 <_ B
    /\
    B <_ 8
  )
  /\
  (
    (
      B =/= 0
      ->
      ( NTP4VCIPow 2 B ) = A
    )
    /\
    (
      B = 0
      ->
      ( NTP4VCNotPowerTwo A )
    )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.

  ntp4vc-all-bits-definition $a |- (
    NTP4VCAllBits A B C D E F G
  ) <-> (
    A. x e. NTP4VCWord32
      (
        ( NTP4VCBitsContract F x )
        ->
        (
          (
            x = 0
            ->
            x = 0
          )
          ->
          (
            (
              x =/= 0
              ->
              ( NTP4VCPowerBranch A B C D E x G )
            )
            /\
            (
              x = 0
              ->
              ( NTP4VCGeneralBranch A B C D E G )
            )
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.

  ntp4vc-all-bases-definition $a |- (
    NTP4VCAllBases A B C D E F
  ) <-> (
    A. x e. NTP4VCWord64
      (
        x = A
        ->
        (
          (
            2 <_ x
            /\
            x <_ ; 2 5 6
          )
          /\
          ( NTP4VCAllBits A B C D E x F )
        )
      )
  ) $.
$}

${
  $(
    Source parameters:
    A=sz, B=un, C=sp, D=up, E=base, and Z=the zone carrier.
  $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.

  ntp4vc-sz-type $e |- A e. NTP4VCWord32 $.
  ntp4vc-un-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-sp-type $e
    |- C e. ( NTP4VCPtr NTP4VCWord8 Z )
  $.
  ntp4vc-up-type $e
    |- D e. ( NTP4VCPtr NTP4VCWord64 Z )
  $.
  ntp4vc-base-type $e |- E e. NTP4VCWord32 $.

  ntp4vc-fact0 $e
    |- 0 < ( NTP4VCSigned32 A )
  $.
  ntp4vc-fact1 $e
    |- 0 < ( NTP4VCSigned32 B )
  $.
  ntp4vc-fact2 $e |- (
    NTP4VCValid C ( NTP4VCSigned32 A )
  ) $.
  ntp4vc-fact3 $e |- (
    NTP4VCValid D ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact4 $e
    |- ( NTP4VCWritable C ) = 1
  $.
  ntp4vc-fact5 $e
    |- ( NTP4VCWritable D ) = 1
  $.
  ntp4vc-fact6 $e |- (
    NTP4VCIPow ( 2 ^ ; 6 4 ) ( NTP4VCSigned32 B )
  ) <_ (
    NTP4VCIPow
      ( NTP4VCSigned32 E )
      ( ( NTP4VCSigned32 A ) - 1 )
  ) $.
  ntp4vc-fact7 $e |- 0 < (
    NTP4VCPelts D
      (
        (
          ( NTP4VCOffset D )
          +
          ( NTP4VCSigned32 B )
        )
        -
        1
      )
  ) $.
  ntp4vc-fact8 $e
    |- 2 <_ ( NTP4VCSigned32 E )
  $.
  ntp4vc-fact9 $e
    |- ( NTP4VCSigned32 E ) <_ ; 2 5 6
  $.
  ntp4vc-fact10 $e |- (
    ( ; 6 4 x. ( NTP4VCSigned32 B ) )
    +
    7
  ) <_ (
    ( 2 ^ ; 3 1 ) - 1
  ) $.

  ntp4vc-pearl-multiprecision-get-str-wmpn-get-str-vc $a |- (
    0 <_ ( NTP4VCSigned32 E )
    /\
    (
      NTP4VCAllBases
        ( NTP4VCSigned32 E )
        D
        ( NTP4VCSigned32 B )
        C
        ( NTP4VCSigned32 A )
        Z
    )
  ) $.
$}
