$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/get_str_Get_str_wmpn_get_str_bitsqtvc: the
  verification condition for converting a positive multiprecision integer
  into base-2^bits digits in a writable byte buffer while preserving the
  loop value invariant and the memory frame. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Fixed-width words are represented by their complete unsigned integer
  carriers, with the exact two's-complement signed interpretation for
  32-bit words. A pointer is represented by its finite data sequence,
  integer offset and bounds, Boolean writability field, and arbitrary
  nonempty zone. Lookup is totalized through the source Int.toNat rule.

  The helper predicates below are definitional factorizations of the
  original Why3 verification condition. NTP4VCCDiv and NTP4VCCMod are
  computer division and remainder (truncation toward zero); the allocation
  quotient uses Euclidean floor division. Proposition-valued conditionals
  are expanded into equivalent exhaustive guarded implications. The final
  declaration is Metamath's native unproved $a statement encoding, and this
  database contains no $p proof declaration.
$)

$c
  NTP4VCWord8 NTP4VCWord32 NTP4VCWord64
  NTP4VCSigned32 NTP4VCInt32InBounds NTP4VCUInt64InBounds
  NTP4VCToNat NTP4VCIPow NTP4VCEDiv NTP4VCCDiv NTP4VCCMod
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCPelts NTP4VCValid NTP4VCAccess
  NTP4VCSameFrame NTP4VCUpdateLaw NTP4VCValue NTP4VCValueBits
  NTP4VCInBase NTP4VCSValueSub NTP4VCSValue NTP4VCFrame
  NTP4VCLoopInvariant NTP4VCStorePost NTP4VCStoreByte
  NTP4VCReduceDigit NTP4VCHighLimb NTP4VCNextLimb
  NTP4VCShiftOverflow NTP4VCShiftSum NTP4VCPositiveStep
  NTP4VCFinishStep NTP4VCLoopStep NTP4VCLoopContract
  NTP4VCInitialState NTP4VCAfterSn NTP4VCAfterE
  NTP4VCAfterO7 NTP4VCAfterO6 NTP4VCAfterO5 NTP4VCAfterO4
  NTP4VCAfterO3 NTP4VCAfterSb NTP4VCAfterO1
$.

ntp4vc-word8-syntax $a class NTP4VCWord8 $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-ipow-syntax $a class ( NTP4VCIPow A B ) $.
ntp4vc-ediv-syntax $a class ( NTP4VCEDiv A B ) $.
ntp4vc-cdiv-syntax $a class ( NTP4VCCDiv A B ) $.
ntp4vc-cmod-syntax $a class ( NTP4VCCMod A B ) $.
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
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-value-bits-syntax $a class ( NTP4VCValueBits A B ) $.
ntp4vc-in-base-syntax $a wff ( NTP4VCInBase A B C D ) $.
ntp4vc-svalue-sub-syntax
  $a class ( NTP4VCSValueSub A B C D ) $.
ntp4vc-svalue-syntax $a class ( NTP4VCSValue A B C ) $.
ntp4vc-frame-syntax $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D E F G H I J ) $.
ntp4vc-store-post-syntax
  $a wff ( NTP4VCStorePost A B C D E F G H I J K ) $.
ntp4vc-store-byte-syntax
  $a wff ( NTP4VCStoreByte A B C D E F G H I J K L M ) $.
ntp4vc-reduce-digit-syntax
  $a wff ( NTP4VCReduceDigit A B C D E F G H I J K L M ) $.
ntp4vc-high-limb-syntax
  $a wff ( NTP4VCHighLimb A B C D E F G H I J K L M N ) $.
ntp4vc-next-limb-syntax
  $a wff ( NTP4VCNextLimb A B C D E F G H I J K L M ) $.
ntp4vc-shift-overflow-syntax
  $a wff ( NTP4VCShiftOverflow A B C D E F G H I J K L M ) $.
ntp4vc-shift-sum-syntax
  $a wff ( NTP4VCShiftSum A B C D E F G H I J K L M ) $.
ntp4vc-positive-step-syntax
  $a wff ( NTP4VCPositiveStep A B C D E F G H I J K ) $.
ntp4vc-finish-step-syntax
  $a wff ( NTP4VCFinishStep A B C D E F G ) $.
ntp4vc-loop-step-syntax
  $a wff ( NTP4VCLoopStep A B C D E F G H I J K L ) $.
ntp4vc-loop-contract-syntax
  $a wff ( NTP4VCLoopContract A B C D E F G H ) $.
ntp4vc-initial-state-syntax
  $a wff ( NTP4VCInitialState A B C D E F G H ) $.
ntp4vc-after-sn-syntax
  $a wff ( NTP4VCAfterSn A B C D E F G ) $.
ntp4vc-after-e-syntax
  $a wff ( NTP4VCAfterE A B C D E F G ) $.
ntp4vc-after-o7-syntax
  $a wff ( NTP4VCAfterO7 A B C D E F G ) $.
ntp4vc-after-o6-syntax
  $a wff ( NTP4VCAfterO6 A B C D E F G H ) $.
ntp4vc-after-o5-syntax
  $a wff ( NTP4VCAfterO5 A B C D E F G H I ) $.
ntp4vc-after-o4-syntax
  $a wff ( NTP4VCAfterO4 A B C D E F G H I ) $.
ntp4vc-after-o3-syntax
  $a wff ( NTP4VCAfterO3 A B C D E F G H ) $.
ntp4vc-after-sb-syntax
  $a wff ( NTP4VCAfterSb A B C D E F G ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E F ) $.

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

ntp4vc-uint64-in-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. NTP4VCWord64
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

ntp4vc-cdiv-definition $a |- (
  NTP4VCCDiv A B
) = if (
  0 <_ A ,
  if (
    0 <_ B ,
    ( |_ ` ( A / B ) ) ,
    ( -u ( |_ ` ( A / ( -u B ) ) ) )
  ) ,
  if (
    0 <_ B ,
    ( -u ( |_ ` ( ( -u A ) / B ) ) ) ,
    ( |_ ` ( ( -u A ) / ( -u B ) ) )
  )
) $.

ntp4vc-cmod-definition $a |- (
  NTP4VCCMod A B
) = (
  A - ( B x. ( NTP4VCCDiv A B ) )
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

ntp4vc-access-definition $a |- (
  NTP4VCAccess A B
) <-> (
  ( NTP4VCMin A )
  <_
  ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B )
  <
  ( NTP4VCMax A )
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
  $d k A $.  $d k B $.  $d k C $.  $d k D $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D
  ) <-> (
    A. k e. ZZ
      (
        ( NTP4VCPelts A k )
        =
        if (
          k = C ,
          D ,
          ( NTP4VCPelts B k )
        )
      )
  ) $.
$}

${
  $d k A $.  $d k B $.

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

ntp4vc-value-bits-definition $a |- (
  NTP4VCValueBits A B
) = if (
  B < 0 ,
  0 ,
  (
    (
      NTP4VCValue A
        ( NTP4VCEDiv B ; 6 4 )
    )
    +
    (
      (
        ( 2 ^ ; 6 4 )
        ^
        ( NTP4VCToNat ( NTP4VCEDiv B ; 6 4 ) )
      )
      x.
      (
        (
          NTP4VCPelts A
            (
              ( NTP4VCOffset A )
              +
              ( NTP4VCEDiv B ; 6 4 )
            )
        )
        mod
        (
          NTP4VCIPow 2
            (
              B
              -
              (
                ; 6 4
                x.
                ( NTP4VCEDiv B ; 6 4 )
              )
            )
        )
      )
    )
  )
) $.

${
  $d k A $.  $d k B $.  $d k C $.  $d k D $.

  ntp4vc-in-base-definition $a |- (
    NTP4VCInBase A B C D
  ) <-> (
    A. k e. ZZ
      (
        (
          C <_ k
          /\
          k < D
        )
        ->
        (
          0 <_ ( NTP4VCPelts B k )
          /\
          ( NTP4VCPelts B k ) < A
        )
      )
  ) $.
$}

${
  $d k A $.  $d k B $.  $d k C $.  $d k D $.

  ntp4vc-svalue-sub-definition $a |- (
    NTP4VCSValueSub A B C D
  ) = (
    sum_ k e. ( 0 ..^ ( NTP4VCToNat ( D - C ) ) )
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
            k
          )
        )
        x.
        ( NTP4VCPelts B ( C + k ) )
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
  $d k A $.  $d k B $.  $d k C $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C
  ) <-> (
    A. k e. ZZ
      (
        (
          k < ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + C ) <_ k
        )
        ->
        (
          ( NTP4VCPelts A k )
          =
          ( NTP4VCPelts B k )
        )
      )
  ) $.
$}

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D E F G H I J
) <-> (
  (
    0 <_ ( NTP4VCSigned32 I )
    /\
    ( NTP4VCSigned32 I ) <_ ( NTP4VCSigned32 D )
  )
  /\
  (
    (
      0 <_ ( NTP4VCSigned32 H )
      /\
      ( NTP4VCSigned32 H ) <_ ( NTP4VCSigned32 F )
    )
    /\
    (
      (
        0 < ( NTP4VCSigned32 H )
        ->
        (
          (
            ( NTP4VCSigned32 F )
            -
            ( NTP4VCSigned32 H )
          )
          x.
          C
        )
        =
        (
          ( ; 6 4 x. ( NTP4VCSigned32 I ) )
          +
          G
        )
      )
      /\
      (
        (
          (
            0 <_ G
            /\
            G < ; 6 4
          )
          \/
          I = D
        )
        /\
        (
          NTP4VCInBase E J
            (
              ( NTP4VCOffset J )
              +
              ( NTP4VCSigned32 H )
            )
            (
              ( NTP4VCOffset J )
              +
              ( NTP4VCSigned32 F )
            )
          /\
          (
            (
              (
                NTP4VCSValueSub E J
                  (
                    ( NTP4VCOffset J )
                    +
                    ( NTP4VCSigned32 H )
                  )
                  (
                    ( NTP4VCOffset J )
                    +
                    ( NTP4VCSigned32 F )
                  )
              )
              =
              (
                NTP4VCValueBits A
                  (
                    (
                      ( NTP4VCSigned32 F )
                      -
                      ( NTP4VCSigned32 H )
                    )
                    x.
                    C
                  )
              )
              /\
              (
                (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 H )
                )
                x.
                C
              )
              <_
              ( ; 6 4 x. ( NTP4VCSigned32 D ) )
            )
            \/
            (
              ( NTP4VCSigned32 H ) = 0
              /\
              (
                NTP4VCSValue E J ( NTP4VCSigned32 F )
              )
              =
              (
                NTP4VCValue A ( NTP4VCSigned32 D )
              )
            )
          )
        )
      )
    )
  )
  /\
  ( NTP4VCFrame J B ( NTP4VCSigned32 F ) )
) $.

ntp4vc-store-post-definition $a |- (
  NTP4VCStorePost A B C D E F G H I J K
) <-> (
  ( NTP4VCSigned32 H ) < ( NTP4VCSigned32 G )
  /\
  (
    (
      0 <_ ( NTP4VCSigned32 I )
      /\
      ( NTP4VCSigned32 I ) <_ ( NTP4VCSigned32 D )
    )
    /\
    (
      (
        0 <_ ( NTP4VCSigned32 H )
        /\
        ( NTP4VCSigned32 H ) <_ ( NTP4VCSigned32 F )
      )
      /\
      (
        (
          (
            ( NTP4VCSigned32 F )
            -
            ( NTP4VCSigned32 H )
          )
          x.
          C
        )
        =
        (
          (
            (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 G )
            )
            x.
            C
          )
          +
          C
        )
        /\
        (
          (
            0 < ( NTP4VCSigned32 H )
            ->
            (
              (
                (
                  ( NTP4VCSigned32 F )
                  -
                  ( NTP4VCSigned32 G )
                )
                x.
                C
              )
              +
              C
            )
            =
            (
              ( ; 6 4 x. ( NTP4VCSigned32 I ) )
              +
              J
            )
          )
          /\
          (
            (
              (
                0 <_ J
                /\
                J < ; 6 4
              )
              \/
              I = D
            )
            /\
            (
              NTP4VCInBase E K
                (
                  ( NTP4VCOffset K )
                  +
                  ( NTP4VCSigned32 H )
                )
                (
                  ( NTP4VCOffset K )
                  +
                  ( NTP4VCSigned32 F )
                )
              /\
              (
                (
                  (
                    NTP4VCSValueSub E K
                      (
                        ( NTP4VCOffset K )
                        +
                        ( NTP4VCSigned32 H )
                      )
                      (
                        ( NTP4VCOffset K )
                        +
                        ( NTP4VCSigned32 F )
                      )
                  )
                  =
                  (
                    NTP4VCValueBits A
                      (
                        (
                          (
                            ( NTP4VCSigned32 F )
                            -
                            ( NTP4VCSigned32 G )
                          )
                          x.
                          C
                        )
                        +
                        C
                      )
                  )
                  /\
                  (
                    (
                      (
                        ( NTP4VCSigned32 F )
                        -
                        ( NTP4VCSigned32 G )
                      )
                      x.
                      C
                    )
                    +
                    C
                  )
                  <_
                  ( ; 6 4 x. ( NTP4VCSigned32 D ) )
                )
                \/
                (
                  ( NTP4VCSigned32 H ) = 0
                  /\
                  (
                    NTP4VCSValue E K ( NTP4VCSigned32 F )
                  )
                  =
                  (
                    NTP4VCValue A ( NTP4VCSigned32 D )
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
  ( NTP4VCFrame K B ( NTP4VCSigned32 F ) )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.  $d x L $.  $d x M $.

  ntp4vc-store-byte-definition $a |- (
    NTP4VCStoreByte A B C D E F G H I J K L M
  ) <-> (
    (
      ( NTP4VCAccess K ( NTP4VCSigned32 H ) )
      /\
      ( NTP4VCWritable K ) = 1
    )
    /\
    A. x e. ( NTP4VCPtr NTP4VCWord8 M )
      (
        ( NTP4VCSameFrame x K )
        ->
        (
          (
            (
              NTP4VCUpdateLaw x K
                (
                  ( NTP4VCOffset x )
                  +
                  ( NTP4VCSigned32 H )
                )
                L
            )
            /\
            (
              NTP4VCPelts x
                (
                  ( NTP4VCOffset x )
                  +
                  ( NTP4VCSigned32 H )
                )
            )
            =
            L
          )
          ->
          (
            NTP4VCStorePost A B C D E F G H I J x
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.  $d x L $.  $d x M $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.  $d y L $.  $d y M $.
  $d x y $.

  ntp4vc-reduce-digit-definition $a |- (
    NTP4VCReduceDigit A B C D E F G H I J K L M
  ) <-> (
    E =/= 0
    /\
    (
      ( NTP4VCUInt64InBounds ( NTP4VCCMod L E ) )
      /\
      A. x e. NTP4VCWord64
        (
          x = ( NTP4VCCMod L E )
          ->
          (
            (
              0 <_ x
              /\
              x <_ ; 2 5 5
            )
            /\
            A. y e. NTP4VCWord8
              (
                y = x
                ->
                (
                  NTP4VCStoreByte
                    A B C D E F G H I J K y M
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.  $d x L $.  $d x M $.  $d x N $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.  $d y L $.  $d y M $.  $d y N $.
  $d x y $.

  ntp4vc-high-limb-definition $a |- (
    NTP4VCHighLimb A B C D E F G H I J K L M N
  ) <-> (
    A. x e. NTP4VCWord64
      (
        x
        =
        (
          (
            (
              NTP4VCPelts A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 K )
                )
            )
            x.
            ( NTP4VCIPow 2 M )
          )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        (
          ( NTP4VCUInt64InBounds ( J + x ) )
          /\
          A. y e. NTP4VCWord64
            (
              y = ( J + x )
              ->
              (
                NTP4VCReduceDigit
                  A B C D E F G H K L I y N
              )
            )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.  $d x L $.  $d x M $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.  $d y L $.  $d y M $.
  $d x y $.

  ntp4vc-next-limb-definition $a |- (
    NTP4VCNextLimb A B C D E F G H I J K L M
  ) <-> (
    ( NTP4VCAccess A ( NTP4VCSigned32 K ) )
    /\
    A. x e. NTP4VCWord64
      (
        x = C
        ->
        (
          ( NTP4VCUInt64InBounds ( x - L ) )
          /\
          A. y e. NTP4VCWord64
            (
              y = ( x - L )
              ->
              (
                (
                  0 <_ y
                  /\
                  y < ; 6 4
                )
                /\
                (
                  NTP4VCHighLimb
                    A B C D E F G H I J K L y M
                )
              )
            )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.  $d x L $.  $d x M $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.  $d y L $.  $d y M $.
  $d x y $.

  ntp4vc-shift-overflow-definition $a |- (
    NTP4VCShiftOverflow A B C D E F G H I J K L M
  ) <-> (
    ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 H ) + 1 ) )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ( NTP4VCSigned32 H ) + 1 )
        ->
        (
          (
            ( NTP4VCSigned32 x ) < ( NTP4VCSigned32 D )
            ->
            (
              ( NTP4VCUInt64InBounds ( L - ; 6 4 ) )
              /\
              A. y e. NTP4VCWord64
                (
                  y = ( L - ; 6 4 )
                  ->
                  (
                    NTP4VCNextLimb
                      A B C D E F G I J K x y M
                  )
                )
            )
          )
          /\
          (
            -.
            ( NTP4VCSigned32 x ) < ( NTP4VCSigned32 D )
            ->
            (
              NTP4VCReduceDigit
                A B C D E F G I x L J K M
            )
          )
        )
      )
  ) $.
$}

ntp4vc-shift-sum-definition $a |- (
  NTP4VCShiftSum A B C D E F G H I J K L M
) <-> (
  (
    ; 6 4 <_ L
    ->
    (
      NTP4VCShiftOverflow
        A B C D E F G H I J K L M
    )
  )
  /\
  (
    -. ; 6 4 <_ L
    ->
    (
      NTP4VCReduceDigit
        A B C D E F G I H L J K M
    )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.
  $d x K $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y E $.
  $d y F $.  $d y G $.  $d y H $.  $d y I $.  $d y J $.
  $d y K $.
  $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.
  $d z F $.  $d z G $.  $d z H $.  $d z I $.  $d z J $.
  $d z K $.
  $d u A $.  $d u B $.  $d u C $.  $d u D $.  $d u E $.
  $d u F $.  $d u G $.  $d u H $.  $d u I $.  $d u J $.
  $d u K $.
  $d x y $.  $d x z $.  $d x u $.
  $d y z $.  $d y u $.  $d z u $.

  ntp4vc-positive-step-definition $a |- (
    NTP4VCPositiveStep A B C D E F G H I J K
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 H ) - 1 )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ( NTP4VCSigned32 H ) - 1 )
        ->
        (
          ( NTP4VCAccess A ( NTP4VCSigned32 I ) )
          /\
          (
            (
              0 <_ G
              /\
              G < ; 6 4
            )
            /\
            A. y e. NTP4VCWord64
              (
                y
                =
                (
                  NTP4VCEDiv
                    (
                      NTP4VCPelts A
                        (
                          ( NTP4VCOffset A )
                          +
                          ( NTP4VCSigned32 I )
                        )
                    )
                    ( NTP4VCIPow 2 G )
                )
                ->
                (
                  ( NTP4VCIPow 2 G ) =/= 0
                  /\
                  A. z e. NTP4VCWord64
                    (
                      z = C
                      ->
                      (
                        ( NTP4VCUInt64InBounds ( G + z ) )
                        /\
                        A. u e. NTP4VCWord64
                          (
                            u = ( G + z )
                            ->
                            (
                              NTP4VCShiftSum
                                A B C D E F H I x J y u K
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
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.

  ntp4vc-finish-step-definition $a |- (
    NTP4VCFinishStep A B C D E F G
  ) <-> (
    0 <_ ( NTP4VCSigned32 F )
    /\
    A. x e. NTP4VCWord32
      (
        x = ( NTP4VCSigned32 F )
        ->
        (
          NTP4VCInBase
            ( NTP4VCIPow 2 C )
            G
            ( NTP4VCOffset G )
            ( ( NTP4VCOffset G ) + x )
          /\
          (
            (
              NTP4VCSValue ( NTP4VCIPow 2 C ) G x
            )
            =
            (
              NTP4VCValue A ( NTP4VCSigned32 D )
            )
            /\
            (
              (
                0 < x
                /\
                x
                <_
                (
                  NTP4VCEDiv
                    (
                      (
                        ( NTP4VCSigned32 E )
                        +
                        C
                      )
                      -
                      1
                    )
                    C
                )
              )
              /\
              (
                0
                <
                (
                  NTP4VCPelts G ( NTP4VCOffset G )
                )
                /\
                (
                  NTP4VCFrame G B
                    (
                      NTP4VCEDiv
                        (
                          (
                            ( NTP4VCSigned32 E )
                            +
                            C
                          )
                          -
                          1
                        )
                        C
                    )
                )
              )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-loop-step-definition $a |- (
  NTP4VCLoopStep A B C D E F G H I J K L
) <-> (
  (
    0 < ( NTP4VCSigned32 I )
    ->
    (
      NTP4VCPositiveStep
        A B C D F G H I J K L
    )
  )
  /\
  (
    -. 0 < ( NTP4VCSigned32 I )
    ->
    (
      NTP4VCFinishStep A B C D E G K
    )
  )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.  $d y H $.
  $d z A $.  $d z B $.  $d z C $.  $d z D $.
  $d z E $.  $d z F $.  $d z G $.  $d z H $.
  $d u A $.  $d u B $.  $d u C $.  $d u D $.
  $d u E $.  $d u F $.  $d u G $.  $d u H $.
  $d x y $.  $d x z $.  $d x u $.
  $d y z $.  $d y u $.  $d z u $.

  ntp4vc-loop-contract-definition $a |- (
    NTP4VCLoopContract A B C D E F G H
  ) <-> (
    A. x e. NTP4VCWord64
      A. y e. NTP4VCWord32
        A. z e. NTP4VCWord32
          A. u e. ( NTP4VCPtr NTP4VCWord8 H )
            (
              ( NTP4VCSameFrame u B )
              ->
              (
                (
                  NTP4VCLoopInvariant
                    A B C D F G x y z u
                )
                ->
                (
                  NTP4VCLoopStep
                    A B C D E F G x y z u H
                )
              )
            )
  ) $.
$}

ntp4vc-initial-state-definition $a |- (
  NTP4VCInitialState A B C D E F G H
) <-> (
  (
    (
      0 <_ 0
      /\
      0 <_ ( NTP4VCSigned32 D )
    )
    /\
    (
      (
        0 <_ ( NTP4VCSigned32 G )
        /\
        ( NTP4VCSigned32 G ) <_ ( NTP4VCSigned32 G )
      )
      /\
      (
        (
          (
            ( NTP4VCSigned32 G )
            -
            ( NTP4VCSigned32 G )
          )
          x.
          C
        )
        =
        0
        /\
        (
          (
            0 < ( NTP4VCSigned32 G )
            ->
            0 = ( ( ; 6 4 x. 0 ) + 0 )
          )
          /\
          (
            (
              (
                0 <_ 0
                /\
                0 < ; 6 4
              )
              \/
              0 = D
            )
            /\
            (
              NTP4VCInBase F B
                (
                  ( NTP4VCOffset B )
                  +
                  ( NTP4VCSigned32 G )
                )
                (
                  ( NTP4VCOffset B )
                  +
                  ( NTP4VCSigned32 G )
                )
              /\
              (
                (
                  (
                    NTP4VCSValueSub F B
                      (
                        ( NTP4VCOffset B )
                        +
                        ( NTP4VCSigned32 G )
                      )
                      (
                        ( NTP4VCOffset B )
                        +
                        ( NTP4VCSigned32 G )
                      )
                  )
                  =
                  ( NTP4VCValueBits A 0 )
                  /\
                  0 <_ ( ; 6 4 x. ( NTP4VCSigned32 D ) )
                )
                \/
                (
                  ( NTP4VCSigned32 G ) = 0
                  /\
                  (
                    NTP4VCSValue F B ( NTP4VCSigned32 G )
                  )
                  =
                  (
                    NTP4VCValue A ( NTP4VCSigned32 D )
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
  ( NTP4VCLoopContract A B C D E F G H )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.
  $d x y $.

  ntp4vc-after-sn-definition $a |- (
    NTP4VCAfterSn A B C D E F G
  ) <-> (
    A. x e. NTP4VCWord64
      (
        x = C
        ->
        (
          (
            (
              0 <_ x
              /\
              x < ; 6 4
            )
            /\
            (
              ( NTP4VCIPow 2 x )
              x.
              1
            )
            <_
            ( ( 2 ^ ; 6 4 ) - 1 )
          )
          /\
          A. y e. NTP4VCWord64
            (
              y = ( ( NTP4VCIPow 2 x ) x. 1 )
              ->
              (
                NTP4VCInitialState
                  A B C D E y F G
              )
            )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.
  $d x y $.

  ntp4vc-after-e-definition $a |- (
    NTP4VCAfterE A B C D E F G
  ) <-> (
    C <_ ( ( 2 ^ ; 3 1 ) - 1 )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x ) = C
        ->
        (
          (
            ( NTP4VCSigned32 x ) =/= 0
            /\
            (
              NTP4VCInt32InBounds
                (
                  NTP4VCCDiv
                    ( NTP4VCSigned32 F )
                    ( NTP4VCSigned32 x )
                )
            )
          )
          /\
          A. y e. NTP4VCWord32
            (
              ( NTP4VCSigned32 y )
              =
              (
                NTP4VCCDiv
                  ( NTP4VCSigned32 F )
                  ( NTP4VCSigned32 x )
              )
              ->
              (
                NTP4VCAfterSn A B C D E y G
              )
            )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.

  ntp4vc-after-o7-definition $a |- (
    NTP4VCAfterO7 A B C D E F G
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 F ) - 1 )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ( NTP4VCSigned32 F ) - 1 )
        ->
        ( NTP4VCAfterE A B C D E x G )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.

  ntp4vc-after-o6-definition $a |- (
    NTP4VCAfterO6 A B C D E F G H
  ) <-> (
    (
      NTP4VCInt32InBounds
        (
          ( NTP4VCSigned32 G )
          +
          ( NTP4VCSigned32 F )
        )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        (
          ( NTP4VCSigned32 G )
          +
          ( NTP4VCSigned32 F )
        )
        ->
        ( NTP4VCAfterO7 A B C D E x H )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.

  ntp4vc-after-o5-definition $a |- (
    NTP4VCAfterO5 A B C D E F G H I
  ) <-> (
    (
      NTP4VCInt32InBounds
        (
          ( NTP4VCSigned32 H )
          +
          ( NTP4VCSigned32 G )
        )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        (
          ( NTP4VCSigned32 H )
          +
          ( NTP4VCSigned32 G )
        )
        ->
        (
          NTP4VCAfterO6 A B C D E F x I
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.

  ntp4vc-after-o4-definition $a |- (
    NTP4VCAfterO4 A B C D E F G H I
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ; 6 4 x. ( NTP4VCSigned32 H ) )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ; 6 4 x. ( NTP4VCSigned32 H ) )
        ->
        (
          NTP4VCAfterO5 A B C D E F G x I
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.  $d x H $.

  ntp4vc-after-o3-definition $a |- (
    NTP4VCAfterO3 A B C D E F G H
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) - 1 )
    )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ( NTP4VCSigned32 D ) - 1 )
        ->
        (
          NTP4VCAfterO4 A B C D E F G x H
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.  $d x G $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.  $d y G $.
  $d x y $.

  ntp4vc-after-sb-definition $a |- (
    NTP4VCAfterSb A B C D E F G
  ) <-> (
    C <_ ( ( 2 ^ ; 3 1 ) - 1 )
    /\
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x ) = C
        ->
        (
          F <_ ( ( 2 ^ ; 3 1 ) - 1 )
          /\
          A. y e. NTP4VCWord32
            (
              ( NTP4VCSigned32 y ) = F
              ->
              (
                NTP4VCAfterO3 A B C D E x y G
              )
            )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d x E $.  $d x F $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.
  $d y E $.  $d y F $.
  $d x y $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E F
  ) <-> (
    A. x e. NTP4VCWord32
      (
        ( NTP4VCSigned32 x )
        =
        ( ( NTP4VCSigned32 D ) - 1 )
        ->
        (
          ( NTP4VCAccess A ( NTP4VCSigned32 x ) )
          /\
          (
            0
            <
            (
              NTP4VCPelts A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 x )
                )
            )
            /\
            A. y e. NTP4VCWord64
              (
                (
                  (
                    1 <_ y
                    /\
                    y <_ ; 6 4
                  )
                  /\
                  (
                    (
                      NTP4VCIPow 2 ( y - 1 )
                    )
                    <_
                    (
                      NTP4VCPelts A
                        (
                          ( NTP4VCOffset A )
                          +
                          ( NTP4VCSigned32 x )
                        )
                    )
                    /\
                    (
                      NTP4VCPelts A
                        (
                          ( NTP4VCOffset A )
                          +
                          ( NTP4VCSigned32 x )
                        )
                    )
                    <
                    ( NTP4VCIPow 2 y )
                  )
                )
                ->
                (
                  NTP4VCAfterSb A B C D E y F
                )
              )
          )
        )
      )
  ) $.
$}

${
  $( Source parameters: A=un, B=up, C=bits, D=sp, E=ub, Z=zone. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-un-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-up-pointer $e
    |- B e. ( NTP4VCPtr NTP4VCWord64 Z )
  $.
  ntp4vc-bits-word32 $e |- C e. NTP4VCWord32 $.
  ntp4vc-sp-pointer $e
    |- D e. ( NTP4VCPtr NTP4VCWord8 Z )
  $.
  ntp4vc-ub-word32 $e |- E e. NTP4VCWord32 $.
  ntp4vc-fact0 $e
    |- 1 <_ ( NTP4VCSigned32 A )
  $.
  ntp4vc-fact1 $e
    |- ( NTP4VCValid B ( NTP4VCSigned32 A ) )
  $.
  ntp4vc-fact2 $e
    |- 1 <_ C
  $.
  ntp4vc-fact3 $e
    |- C <_ 8
  $.
  ntp4vc-fact4 $e |- (
    NTP4VCValid D
      (
        NTP4VCEDiv
          (
            (
              ( NTP4VCSigned32 E )
              +
              C
            )
            -
            1
          )
          C
      )
  ) $.
  ntp4vc-fact5 $e
    |- 0 <_ ( NTP4VCSigned32 E )
  $.
  ntp4vc-fact6 $e |- (
    NTP4VCValue B ( NTP4VCSigned32 A )
  ) < (
    NTP4VCIPow 2 ( NTP4VCSigned32 E )
  ) $.
  ntp4vc-fact7 $e |- 0 < (
    NTP4VCPelts B
      (
        (
          ( NTP4VCOffset B )
          +
          ( NTP4VCSigned32 A )
        )
        -
        1
      )
  ) $.
  ntp4vc-fact8 $e |- (
    ( ; 6 4 x. ( NTP4VCSigned32 A ) )
    +
    7
  ) <_ (
    ( 2 ^ ; 3 1 ) - 1
  ) $.
  ntp4vc-fact9 $e
    |- ( NTP4VCWritable D ) = 1
  $.

  ntp4vc-pearl-multiprecision-get-str-wmpn-get-str-bits-vc $a |- (
    NTP4VCInt32InBounds
      ( ( NTP4VCSigned32 A ) - 1 )
  ) /\ (
    NTP4VCAfterO1 B D C A E Z
  ) $.
$}
