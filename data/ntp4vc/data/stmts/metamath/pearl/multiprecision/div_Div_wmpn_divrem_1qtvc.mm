$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_wmpn_divrem_1qtvc: the verification condition
  for one-limb multiprecision division, including divisor normalization,
  reciprocal division, pointer and quotient updates, loop invariants, and
  the final quotient/remainder specification. This file contains no proof.

  The source 32- and 64-bit words are represented by their complete canonical
  integer carriers, with exact two's-complement signed interpretation for
  32-bit words. Pointer data retains a total ZZ-indexed limb map and an
  independent nonnegative length, together with offset, bounds, an explicit
  two-element writability carrier, and an arbitrary zone. Functional update
  is extensional, and ValueSub is the exact little-endian radix-2^64 finite
  sum. The named predicates below are only definitional factorizations of the
  official generated verification condition; all source quantifiers,
  implications, and conditional branches remain internal to the statement.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCDataCarrier NTP4VCPtr
  NTP4VCSigned32 NTP4VCInt32InBounds NTP4VCUInt64InBounds NTP4VCToNat
  NTP4VCData NTP4VCLength NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone
  NTP4VCPelts NTP4VCMapBase NTP4VCMapUpdate NTP4VCMapGet
  NTP4VCValueSub NTP4VCValue NTP4VCIPow NTP4VCValid
  NTP4VCReciprocal NTP4VCSameShape NTP4VCInRange
  NTP4VCNormInv NTP4VCPlainInv NTP4VCNormNext NTP4VCPlainNext
  NTP4VCNormStore NTP4VCPlainStore
  NTP4VCNormDivision NTP4VCPlainDivision
  NTP4VCNormAfterO3 NTP4VCNormAfterLH
  NTP4VCNormStep NTP4VCNormFinal NTP4VCNormLoopBody NTP4VCNormLoop
  NTP4VCNormInitial NTP4VCNormAfterRy NTP4VCNormAfterO1
  NTP4VCPositiveBranch
  NTP4VCPlainStep NTP4VCPlainFinal NTP4VCPlainLoopBody
  NTP4VCPlainLoop NTP4VCPlainInitial NTP4VCZeroBranch
  NTP4VCClzBody NTP4VCAfterClz NTP4VCMain
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-data-carrier-syn $a class NTP4VCDataCarrier $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-bounds-syn $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint64-bounds-syn $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
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
ntp4vc-valid-syn $a wff ( NTP4VCValid A B ) $.
ntp4vc-reciprocal-syn $a wff ( NTP4VCReciprocal A B ) $.
ntp4vc-same-shape-syn $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-in-range-syn $a wff ( NTP4VCInRange A B ) $.
ntp4vc-norm-inv-syn
  $a wff ( NTP4VCNormInv A B C D E F G H ) $.
ntp4vc-plain-inv-syn
  $a wff ( NTP4VCPlainInv A B C D E F G ) $.
ntp4vc-norm-next-syn
  $a wff ( NTP4VCNormNext A B C D E F G H I ) $.
ntp4vc-plain-next-syn
  $a wff ( NTP4VCPlainNext A B C D E F G H ) $.
ntp4vc-norm-store-syn
  $a wff ( NTP4VCNormStore A B C D E F G H I ) $.
ntp4vc-plain-store-syn
  $a wff ( NTP4VCPlainStore A B C D E F G H ) $.
ntp4vc-norm-division-syn
  $a wff ( NTP4VCNormDivision A B C D E F G H I ) $.
ntp4vc-plain-division-syn
  $a wff ( NTP4VCPlainDivision A B C D E F G ) $.
ntp4vc-norm-after-o3-syn
  $a wff ( NTP4VCNormAfterO3 A B C D E F G H I J K ) $.
ntp4vc-norm-after-lh-syn
  $a wff ( NTP4VCNormAfterLH A B C D E F G H I J ) $.
ntp4vc-norm-step-syn
  $a wff ( NTP4VCNormStep A B C D E F G H I J ) $.
ntp4vc-norm-final-syn
  $a wff ( NTP4VCNormFinal A B C D E F ) $.
ntp4vc-norm-loop-body-syn
  $a wff ( NTP4VCNormLoopBody A B C D E F G H I J K ) $.
ntp4vc-norm-loop-syn
  $a wff ( NTP4VCNormLoop A B C D E F G H I ) $.
ntp4vc-norm-initial-syn
  $a wff ( NTP4VCNormInitial A B C D E F G H I ) $.
ntp4vc-norm-after-ry-syn
  $a wff ( NTP4VCNormAfterRy A B C D E F G ) $.
ntp4vc-norm-after-o1-syn
  $a wff ( NTP4VCNormAfterO1 A B C D E F ) $.
ntp4vc-positive-branch-syn
  $a wff ( NTP4VCPositiveBranch A B C D E F ) $.
ntp4vc-plain-step-syn
  $a wff ( NTP4VCPlainStep A B C D E F G H ) $.
ntp4vc-plain-final-syn
  $a wff ( NTP4VCPlainFinal A B C D E ) $.
ntp4vc-plain-loop-body-syn
  $a wff ( NTP4VCPlainLoopBody A B C D E F G H ) $.
ntp4vc-plain-loop-syn
  $a wff ( NTP4VCPlainLoop A B C D E F ) $.
ntp4vc-plain-initial-syn
  $a wff ( NTP4VCPlainInitial A B C D E F ) $.
ntp4vc-zero-branch-syn
  $a wff ( NTP4VCZeroBranch A B C D E ) $.
ntp4vc-clz-body-syn
  $a wff ( NTP4VCClzBody A B C D E F ) $.
ntp4vc-after-clz-syn
  $a wff ( NTP4VCAfterClz A B C D E ) $.
ntp4vc-main-syn $a wff ( NTP4VCMain A B C D ) $.

ntp4vc-word32-def $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.
ntp4vc-word64-def $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.
ntp4vc-data-carrier-def $a |- NTP4VCDataCarrier =
  ( ( NTP4VCWord64 ^m ZZ ) X. NN0 ) $.
ntp4vc-ptr-def $a |- ( NTP4VCPtr A ) =
  ( NTP4VCDataCarrier X.
    ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) ) ) $.
ntp4vc-signed32-def $a |- ( NTP4VCSigned32 A ) =
  if ( A < ( 2 ^ ; 3 1 ) , A , ( A - ( 2 ^ ; 3 2 ) ) ) $.
ntp4vc-int32-bounds-def $a |- ( NTP4VCInt32InBounds A ) <-> (
  ( A e. ZZ )
  /\
  ( ( -u ( 2 ^ ; 3 1 ) ) <_ A /\ A < ( 2 ^ ; 3 1 ) )
) $.
ntp4vc-uint64-bounds-def $a |- ( NTP4VCUInt64InBounds A ) <->
  ( A e. NTP4VCWord64 ) $.
ntp4vc-to-nat-def $a |- ( NTP4VCToNat A ) =
  if ( 0 <_ A , A , 0 ) $.
ntp4vc-data-def $a |- ( NTP4VCData A ) = ( 1st ` A ) $.
ntp4vc-length-def $a |- ( NTP4VCLength A ) =
  ( 2nd ` ( NTP4VCData A ) ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) =
  ( 1st ` ( 2nd ` A ) ) $.
ntp4vc-min-def $a |- ( NTP4VCMin A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.
ntp4vc-max-def $a |- ( NTP4VCMax A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.
ntp4vc-writable-def $a |- ( NTP4VCWritable A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.
ntp4vc-zone-def $a |- ( NTP4VCZone A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.
ntp4vc-pelts-def $a |- ( NTP4VCPelts A B ) =
  ( ( 1st ` ( NTP4VCData A ) ) ` B ) $.

${
  $d z A $.
  ntp4vc-map-base-def $a |- ( NTP4VCMapBase A ) =
    ( 1st ` ( NTP4VCData A ) ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.
  ntp4vc-map-update-def $a |- ( NTP4VCMapUpdate A B C ) =
    ( z e. ZZ |-> if ( z = B , C , ( A ` z ) ) ) $.
$}

ntp4vc-map-get-def $a |- ( NTP4VCMapGet A B ) = ( A ` B ) $.

${
  $d z A $.  $d z B $.  $d z C $.
  ntp4vc-value-sub-def $a |- ( NTP4VCValueSub A B C ) =
    sum_ z e. ( 0 ..^ ( NTP4VCToNat ( C - B ) ) )
      ( ( NTP4VCMapGet A ( B + z ) ) x. ( ( 2 ^ ; 6 4 ) ^ z ) ) $.
$}

ntp4vc-value-def $a |- ( NTP4VCValue A B ) =
  ( NTP4VCValueSub
    ( NTP4VCMapBase A )
    ( NTP4VCOffset A )
    ( ( NTP4VCOffset A ) + B )
  ) $.

ntp4vc-ipow-def $a |- ( NTP4VCIPow A B ) =
  ( A ^ ( NTP4VCToNat B ) ) $.

ntp4vc-valid-def $a |- ( NTP4VCValid A B ) <-> (
  ( NTP4VCInt32InBounds B )
  /\
  (
    0 <_ B
    /\
    (
      0 <_ ( NTP4VCMin A )
      /\
      (
        ( NTP4VCMin A ) <_ ( NTP4VCOffset A )
        /\
        (
          ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A )
          /\
          ( NTP4VCMax A ) <_ ( NTP4VCLength A )
        )
      )
    )
  )
) $.

ntp4vc-reciprocal-def $a |- ( NTP4VCReciprocal A B ) <-> (
  A =
  (
    ( |_ `
      (
        (
          (
            ( 2 ^ ; 6 4 )
            x.
            ( 2 ^ ; 6 4 )
          )
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

ntp4vc-same-shape-def $a |- ( NTP4VCSameShape A B ) <-> (
  ( ( NTP4VCLength A ) = ( NTP4VCLength B ) )
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

ntp4vc-in-range-def $a |- ( NTP4VCInRange A B ) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A )
) $.

$(
  NTP4VCNormInv X Sz Q Msb Ry Mult R I is the normalized-loop invariant.
$)
ntp4vc-norm-inv-def $a |- (
  NTP4VCNormInv A B C D E F G H
) <-> (
  (
    ( -u 1 ) <_ ( NTP4VCSigned32 H )
    /\
    ( NTP4VCSigned32 H ) <_ ( NTP4VCSigned32 D )
  )
  /\
  (
    G < E
    /\
    (
      (
        F
        x.
        (
          NTP4VCValueSub
          ( NTP4VCMapBase A )
          ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 H ) ) + 1 )
          ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) )
        )
      )
      =
      (
        (
          NTP4VCValueSub
          ( NTP4VCMapBase C )
          ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 H ) ) + 1 )
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
        )
        x.
        E
      )
      +
      G
    )
    /\
    (
      G <_ ( ( 2 ^ ; 6 4 ) - F )
      /\
      ( G mod F ) = 0
    )
  )
) $.

ntp4vc-plain-inv-def $a |- (
  NTP4VCPlainInv A B C D E F G
) <-> (
  (
    ( -u 1 ) <_ ( NTP4VCSigned32 G )
    /\
    ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 D )
  )
  /\
  (
    F < E
    /\
    (
      (
        NTP4VCValueSub
        ( NTP4VCMapBase A )
        ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 G ) ) + 1 )
        ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) )
      )
      =
      (
        (
          NTP4VCValueSub
          ( NTP4VCMapBase C )
          ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 G ) ) + 1 )
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
        )
        x.
        E
      )
      +
      F
    )
  )
) $.

$(
  NTP4VCNormNext X Sz Q2 Msb Ry Mult Rem O8 I is the invariant after
  storing one quotient limb and decrementing I to O8.
$)
ntp4vc-norm-next-def $a |- (
  NTP4VCNormNext A B C D E F G H I
) <-> (
  ( NTP4VCSigned32 H ) < ( NTP4VCSigned32 I )
  /\
  (
    (
      ( -u 1 ) <_ ( NTP4VCSigned32 H )
      /\
      ( NTP4VCSigned32 H ) <_ ( NTP4VCSigned32 D )
    )
    /\
    (
      G < E
      /\
      (
        (
          F
          x.
          (
            NTP4VCValueSub
            ( NTP4VCMapBase A )
            ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 H ) ) + 1 )
            ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) )
          )
        )
        =
        (
          (
            NTP4VCValueSub
            ( NTP4VCMapBase C )
            ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 H ) ) + 1 )
            ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
          )
          x.
          E
        )
        +
        G
      )
      /\
      (
        G <_ ( ( 2 ^ ; 6 4 ) - F )
        /\
        ( G mod F ) = 0
      )
    )
  )
) $.

ntp4vc-plain-next-def $a |- (
  NTP4VCPlainNext A B C D E F G H
) <-> (
  ( NTP4VCSigned32 G ) < ( NTP4VCSigned32 H )
  /\
  (
    (
      ( -u 1 ) <_ ( NTP4VCSigned32 G )
      /\
      ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 D )
    )
    /\
    (
      F < E
      /\
      (
        NTP4VCValueSub
        ( NTP4VCMapBase A )
        ( ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 G ) ) + 1 )
        ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 B ) )
      )
      =
      (
        (
          NTP4VCValueSub
          ( NTP4VCMapBase C )
          ( ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 G ) ) + 1 )
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
        )
        x.
        E
      )
      +
      F
    )
  )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y z $.

  ntp4vc-norm-store-def $a |- (
    NTP4VCNormStore A B C D E F G H I
  ) <-> (
    (
      (
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 G ) )
        <_
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      /\
      (
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 G ) )
        <
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 G ) )
        \/
        (
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
          <_
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 G ) )
        )
      )
    )
    /\
    (
      (
        NTP4VCValueSub
        ( NTP4VCMapBase C )
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 G ) )
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      =
      (
        NTP4VCValueSub
        (
          NTP4VCMapUpdate
          ( NTP4VCMapBase C )
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 G ) )
          H
        )
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 G ) )
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      ->
      (
        (
          ( NTP4VCInRange C ( NTP4VCSigned32 G ) )
          /\
          ( NTP4VCWritable C ) = 1
        )
        /\
        A. z
          (
            z e. ( NTP4VCPtr _V )
            ->
            (
              ( NTP4VCSameShape z C )
              ->
              (
                (
                  ( NTP4VCMapBase z )
                  =
                  (
                    NTP4VCMapUpdate
                    ( NTP4VCMapBase C )
                    ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 G ) )
                    H
                  )
                )
                /\
                (
                  NTP4VCPelts
                  z
                  ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 G ) )
                )
                =
                H
              )
              ->
              (
                ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 G ) - 1 ) )
                /\
                A. y
                  (
                    y e. NTP4VCWord32
                    ->
                    (
                      ( NTP4VCSigned32 y )
                      =
                      ( ( NTP4VCSigned32 G ) - 1 )
                      ->
                      (
                        NTP4VCNormNext
                        A B z D E F I y G
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
  $d z A $.  $d z B $.  $d z C $.  $d z D $.
  $d z E $.  $d z F $.  $d z G $.  $d z H $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.  $d y H $.  $d y z $.

  ntp4vc-plain-store-def $a |- (
    NTP4VCPlainStore A B C D E F G H
  ) <-> (
    (
      (
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 F ) )
        <_
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      /\
      (
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 F ) )
        <
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 F ) )
        \/
        (
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
          <_
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 F ) )
        )
      )
    )
    /\
    (
      (
        NTP4VCValueSub
        ( NTP4VCMapBase C )
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 F ) )
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      =
      (
        NTP4VCValueSub
        (
          NTP4VCMapUpdate
          ( NTP4VCMapBase C )
          ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 F ) )
          G
        )
        ( ( ( NTP4VCOffset C ) + 1 ) + ( NTP4VCSigned32 F ) )
        ( ( NTP4VCOffset C ) + ( NTP4VCSigned32 B ) )
      )
      ->
      (
        (
          ( NTP4VCInRange C ( NTP4VCSigned32 F ) )
          /\
          ( NTP4VCWritable C ) = 1
        )
        /\
        A. z
          (
            z e. ( NTP4VCPtr _V )
            ->
            (
              ( NTP4VCSameShape z C )
              ->
              (
                (
                  ( NTP4VCMapBase z )
                  =
                  (
                    NTP4VCMapUpdate
                    ( NTP4VCMapBase C )
                    ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 F ) )
                    G
                  )
                )
                /\
                (
                  NTP4VCPelts
                  z
                  ( ( NTP4VCOffset z ) + ( NTP4VCSigned32 F ) )
                )
                =
                G
              )
              ->
              (
                ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 F ) - 1 ) )
                /\
                A. y
                  (
                    y e. NTP4VCWord32
                    ->
                    (
                      ( NTP4VCSigned32 y )
                      =
                      ( ( NTP4VCSigned32 F ) - 1 )
                      ->
                      (
                        NTP4VCPlainNext
                        A B z D E H y F
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
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y z $.

  ntp4vc-norm-division-def $a |- (
    NTP4VCNormDivision A B C D E F G H I
  ) <-> (
    A. z
      A. y
        (
          (
            z e. NTP4VCWord64
            /\
            y e. NTP4VCWord64
          )
          ->
          (
            (
              ( ( z x. E ) + y )
              =
              ( H + ( ( 2 ^ ; 6 4 ) x. I ) )
            )
            /\
            (
              0 <_ y
              /\
              y < E
            )
          )
          ->
          (
            -. ( F = 0 )
            /\
            ( NTP4VCNormStore A B C D E F G z y )
          )
        )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.
  $d z E $.  $d z F $.  $d z G $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.  $d y z $.

  ntp4vc-plain-division-def $a |- (
    NTP4VCPlainDivision A B C D E F G
  ) <-> (
    A. z
      A. y
        (
          (
            z e. NTP4VCWord64
            /\
            y e. NTP4VCWord64
          )
          ->
          (
            (
              ( ( z x. E ) + y )
              =
              (
                (
                  NTP4VCPelts
                  A
                  ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 F ) )
                )
                +
                ( ( 2 ^ ; 6 4 ) x. G )
              )
            )
            /\
            (
              0 <_ y
              /\
              y < E
            )
          )
          ->
          ( NTP4VCPlainStore A B C D E F z y )
        )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.  $d z J $.
  $d z K $.

  ntp4vc-norm-after-o3-def $a |- (
    NTP4VCNormAfterO3 A B C D E F G H I J K
  ) <-> (
    A. z
      (
        z e. NTP4VCWord64
        ->
        (
          z = ( H + I )
          ->
          (
            (
              ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ E
              /\
              (
                z < E
                /\
                ( NTP4VCReciprocal K E )
              )
            )
            /\
            ( NTP4VCNormDivision A B C D E F G J z )
          )
        )
      )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.  $d z J $.
  $d z K $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.  $d y z $.

  ntp4vc-norm-after-lh-def $a |- (
    NTP4VCNormAfterLH A B C D E F G H I J
  ) <-> (
    A. z
      A. y
        (
          (
            z e. NTP4VCWord64
            /\
            y e. NTP4VCWord64
          )
          ->
          (
            (
              z + ( ( 2 ^ ; 6 4 ) x. y )
            )
            =
            (
              ( NTP4VCIPow 2 J )
              x.
              (
                NTP4VCPelts
                A
                ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 G ) )
              )
            )
            /\
            (
              ( z mod ( NTP4VCIPow 2 J ) ) = 0
              /\
              (
                z <_ ( ( 2 ^ ; 6 4 ) - ( NTP4VCIPow 2 J ) )
                /\
                y < ( NTP4VCIPow 2 J )
              )
            )
          )
          ->
          (
            ( NTP4VCUInt64InBounds ( H + y ) )
            /\
            ( NTP4VCNormAfterO3 A B C D E F G H y z I )
          )
        )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.  $d z J $.

  ntp4vc-norm-step-def $a |- (
    NTP4VCNormStep A B C D E F G H I J
  ) <-> (
    ( NTP4VCInRange A ( NTP4VCSigned32 H ) )
    /\
    (
      0 <_ ( NTP4VCSigned32 E )
      /\
      A. z
        (
          z e. NTP4VCWord64
          ->
          (
            z = ( NTP4VCSigned32 E )
            ->
            (
              (
                0 < z
                /\
                z < ; 6 4
              )
              /\
              (
                NTP4VCNormAfterLH
                A B C D F G H I J z
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y z $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x y $.  $d x z $.
  $d w A $.  $d w B $.  $d w C $.  $d w D $.  $d w E $.
  $d w F $.  $d w x $.  $d w y $.  $d w z $.

  ntp4vc-norm-final-def $a |- (
    NTP4VCNormFinal A B C D E F
  ) <-> (
    0 <_ ( NTP4VCSigned32 D )
    /\
    A. z
      (
        z e. NTP4VCWord64
        ->
        (
          z = ( NTP4VCSigned32 D )
          ->
          (
            (
              (
                0 <_ z
                /\
                z < ; 6 4
              )
              /\
              ( F mod ( NTP4VCIPow 2 z ) ) = 0
            )
            /\
            A. y
              (
                y e. NTP4VCWord64
                ->
                (
                  F = ( ( NTP4VCIPow 2 z ) x. y )
                  ->
                  (
                    0 <_ ( NTP4VCSigned32 D )
                    /\
                    A. x
                      (
                        x e. NTP4VCWord64
                        ->
                        (
                          x = ( NTP4VCSigned32 D )
                          ->
                          (
                            (
                              (
                                0 <_ x
                                /\
                                x < ; 6 4
                              )
                              /\
                              ( F mod ( NTP4VCIPow 2 x ) ) = 0
                            )
                            /\
                            A. w
                              (
                                w e. NTP4VCWord64
                                ->
                                (
                                  F = ( ( NTP4VCIPow 2 x ) x. w )
                                  ->
                                  (
                                    (
                                      NTP4VCValue
                                      A
                                      ( NTP4VCSigned32 B )
                                    )
                                    =
                                    (
                                      (
                                        NTP4VCValue
                                        C
                                        ( NTP4VCSigned32 B )
                                      )
                                      x.
                                      E
                                    )
                                    +
                                    w
                                  )
                                  /\
                                  w < E
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

ntp4vc-norm-loop-body-def $a |- (
  NTP4VCNormLoopBody A B C D E F G H I J K
) <-> (
  (
    0 <_ ( NTP4VCSigned32 I )
    ->
    ( NTP4VCNormStep A B C D E G H I J K )
  )
  /\
  (
    -. 0 <_ ( NTP4VCSigned32 I )
    ->
    ( NTP4VCNormFinal A B C E F J )
  )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y z $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.
  $d x y $.  $d x z $.

  ntp4vc-norm-loop-def $a |- (
    NTP4VCNormLoop A B C D E F G H I
  ) <-> (
    A. z
      A. y
        A. x
          (
            (
              z e. NTP4VCWord64
              /\
              (
                y e. NTP4VCWord32
                /\
                x e. ( NTP4VCPtr _V )
              )
            )
            ->
            (
              ( NTP4VCSameShape x C )
              ->
              (
                ( NTP4VCNormInv A B x D G H z y )
                ->
                (
                  NTP4VCNormLoopBody
                  A B x D E F G H y z I
                )
              )
            )
          )
  ) $.
$}

ntp4vc-norm-initial-def $a |- (
  NTP4VCNormInitial A B C D E F G H I
) <-> (
  ( NTP4VCNormInv A B C D G H 0 D )
  /\
  ( NTP4VCNormLoop A B C D E F G H I )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y z $.

  ntp4vc-norm-after-ry-def $a |- (
    NTP4VCNormAfterRy A B C D E F G
  ) <-> (
    A. z
      (
        z e. NTP4VCWord64
        ->
        (
          z = ( ( NTP4VCIPow 2 G ) x. F )
          ->
          (
            ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ z
            /\
            A. y
              (
                y e. NTP4VCWord64
                ->
                (
                  ( NTP4VCReciprocal y z )
                  ->
                  (
                    NTP4VCNormInitial
                    A B C D E F z ( NTP4VCIPow 2 G ) y
                  )
                )
              )
          )
        )
      )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.

  ntp4vc-norm-after-o1-def $a |- (
    NTP4VCNormAfterO1 A B C D E F
  ) <-> (
    A. z
      (
        z e. NTP4VCWord64
        ->
        (
          z = ( NTP4VCSigned32 E )
          ->
          (
            (
              (
                0 <_ z
                /\
                z < ; 6 4
              )
              /\
              ( ( NTP4VCIPow 2 z ) x. F ) <_ ( ( 2 ^ ; 6 4 ) - 1 )
            )
            /\
            ( NTP4VCNormAfterRy A B C D E F z )
          )
        )
      )
  ) $.
$}

ntp4vc-positive-branch-def $a |- (
  NTP4VCPositiveBranch A B C D E F
) <-> (
  0 <_ ( NTP4VCSigned32 E )
  /\
  ( NTP4VCNormAfterO1 A B C D E F )
) $.

ntp4vc-plain-step-def $a |- (
  NTP4VCPlainStep A B C D E F G H
) <-> (
  ( NTP4VCInRange A ( NTP4VCSigned32 F ) )
  /\
  (
    (
      ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ E
      /\
      (
        G < E
        /\
        ( NTP4VCReciprocal H E )
      )
    )
    /\
    ( NTP4VCPlainDivision A B C D E F G )
  )
) $.

ntp4vc-plain-final-def $a |- (
  NTP4VCPlainFinal A B C D E
) <-> (
  (
    NTP4VCValue
    A
    ( NTP4VCSigned32 B )
  )
  =
  (
    (
      NTP4VCValue
      C
      ( NTP4VCSigned32 B )
    )
    x.
    D
  )
  +
  E
  /\
  E < D
) $.

ntp4vc-plain-loop-body-def $a |- (
  NTP4VCPlainLoopBody A B C D E F G H
) <-> (
  (
    0 <_ ( NTP4VCSigned32 F )
    ->
    ( NTP4VCPlainStep A B C D E F G H )
  )
  /\
  (
    -. 0 <_ ( NTP4VCSigned32 F )
    ->
    ( NTP4VCPlainFinal A B C E G )
  )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y z $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x y $.  $d x z $.

  ntp4vc-plain-loop-def $a |- (
    NTP4VCPlainLoop A B C D E F
  ) <-> (
    A. z
      A. y
        A. x
          (
            (
              z e. NTP4VCWord64
              /\
              (
                y e. NTP4VCWord32
                /\
                x e. ( NTP4VCPtr _V )
              )
            )
            ->
            (
              ( NTP4VCSameShape x C )
              ->
              (
                ( NTP4VCPlainInv A B x D E z y )
                ->
                (
                  NTP4VCPlainLoopBody
                  A B x D E y z F
                )
              )
            )
          )
  ) $.
$}

ntp4vc-plain-initial-def $a |- (
  NTP4VCPlainInitial A B C D E F
) <-> (
  ( NTP4VCPlainInv A B C D E 0 D )
  /\
  ( NTP4VCPlainLoop A B C D E F )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.

  ntp4vc-zero-branch-def $a |- (
    NTP4VCZeroBranch A B C D E
  ) <-> (
    ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) ) <_ E
    /\
    A. z
      (
        z e. NTP4VCWord64
        ->
        (
          ( NTP4VCReciprocal z E )
          ->
          ( NTP4VCPlainInitial A B C D E z )
        )
      )
  ) $.
$}

ntp4vc-clz-body-def $a |- (
  NTP4VCClzBody A B C D E F
) <-> (
  (
    0 < ( NTP4VCSigned32 E )
    ->
    ( NTP4VCPositiveBranch A B C D E F )
  )
  /\
  (
    -. 0 < ( NTP4VCSigned32 E )
    ->
    ( NTP4VCZeroBranch A B C D F )
  )
) $.

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.

  ntp4vc-after-clz-def $a |- (
    NTP4VCAfterClz A B C D E
  ) <-> (
    A. z
      (
        z e. NTP4VCWord32
        ->
        (
          (
            (
              ( ( NTP4VCIPow 2 ( NTP4VCSigned32 z ) ) x. D )
              <_
              ( ( 2 ^ ; 6 4 ) - 1 )
            )
            /\
            (
              ( ( 2 ^ ; 6 4 ) - 1 )
              <
              (
                2
                x.
                (
                  ( NTP4VCIPow 2 ( NTP4VCSigned32 z ) )
                  x.
                  D
                )
              )
            )
            /\
            (
              0 <_ ( NTP4VCSigned32 z )
              /\
              ( NTP4VCSigned32 z ) < ; 6 4
            )
          )
          ->
          ( NTP4VCClzBody A B C E z D )
        )
      )
  ) $.
$}

${
  $d z A $.  $d z B $.  $d z C $.  $d z D $.

  ntp4vc-main-def $a |- (
    NTP4VCMain A B C D
  ) <-> (
    A. z
      (
        z e. NTP4VCWord32
        ->
        (
          ( NTP4VCSigned32 z )
          =
          ( ( NTP4VCSigned32 B ) - 1 )
          ->
          (
            0 < D
            /\
            ( NTP4VCAfterClz A B C D z )
          )
        )
      )
  ) $.
$}

${
  $( Source parameters: A=x, B=sz, C=q, and D=y. $)

  ntp4vc-x-ptr $e |- A e. ( NTP4VCPtr _V ) $.
  ntp4vc-sz-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-q-ptr $e |- C e. ( NTP4VCPtr _V ) $.
  ntp4vc-y-word64 $e |- D e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- (
    NTP4VCValid C ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact2 $e |- ( NTP4VCWritable C ) = 1 $.
  ntp4vc-fact3 $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-fact4 $e |- 0 < D $.

  ntp4vc-pearl-multiprecision-div-wmpn-divrem-1-vc $a |- (
    ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 B ) - 1 ) )
    /\
    ( NTP4VCMain A B C D )
  ) $.
$}
