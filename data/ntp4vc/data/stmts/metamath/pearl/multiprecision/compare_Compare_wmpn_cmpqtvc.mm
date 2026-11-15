$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/compare_Compare_wmpn_cmpqtvc: the verification
  condition for comparing two valid equal-length multiprecision unsigned
  integers by scanning their 64-bit limbs from most to least significant.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Unsigned 32- and 64-bit words are represented by their complete canonical
  integer carriers. NTP4VCSigned32 is the exact two's-complement signed
  interpretation of a 32-bit word. A pointer retains the source finite limb
  sequence, integer offset and bounds, Boolean writability field, and zone.
  NTP4VCPelts is the source totalized lookup through Int.toNat, and
  NTP4VCValue is the little-endian radix-2^64 interpretation of a pointer
  prefix.

  The range, address, decrement, limb-decision, and loop-step predicates are
  definitional factorizations of the original verification condition.
  Proposition-valued conditionals are expanded into equivalent exhaustive
  guarded implications. The scoped essential hypotheses represent exactly
  the source typed parameters and two pointer-validity assumptions. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact file contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCToNat NTP4VCPelts NTP4VCValid NTP4VCValue
  NTP4VCCompareInt NTP4VCComparison NTP4VCRangeEqual
  NTP4VCAddressValid NTP4VCContinue NTP4VCLimbDecision
  NTP4VCDecrement NTP4VCLoopInvariant NTP4VCLoopStep
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-ptr-syntax $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syntax $a class ( NTP4VCData A ) $.
ntp4vc-offset-syntax $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syntax $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-compare-int-syntax $a class ( NTP4VCCompareInt A B ) $.
ntp4vc-comparison-syntax $a class ( NTP4VCComparison A B C ) $.
ntp4vc-range-equal-syntax
  $a wff ( NTP4VCRangeEqual A B C D ) $.
ntp4vc-address-valid-syntax
  $a wff ( NTP4VCAddressValid A B ) $.
ntp4vc-continue-syntax
  $a wff ( NTP4VCContinue A B C D E ) $.
ntp4vc-limb-decision-syntax
  $a wff ( NTP4VCLimbDecision A B C D E ) $.
ntp4vc-decrement-syntax
  $a wff ( NTP4VCDecrement A B C D ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D ) $.
ntp4vc-loop-step-syntax
  $a wff ( NTP4VCLoopStep A B C D ) $.

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

ntp4vc-offset-definition $a |- (
  NTP4VCOffset A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

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

ntp4vc-compare-int-definition $a |- (
  NTP4VCCompareInt A B
) = if (
  A < B ,
  ( -u 1 ) ,
  if ( A = B , 0 , 1 )
) $.

ntp4vc-comparison-definition $a |- (
  NTP4VCComparison A B C
) = (
  NTP4VCCompareInt
    ( NTP4VCValue A ( NTP4VCSigned32 C ) )
    ( NTP4VCValue B ( NTP4VCSigned32 C ) )
) $.

${
  $d j A B C D $.

  ntp4vc-range-equal-definition $a |- (
    NTP4VCRangeEqual A B C D
  ) <-> (
    A. j e. ZZ
      (
        (
          C <_ j
          /\
          j < D
        )
        ->
        (
          NTP4VCPelts A ( ( NTP4VCOffset A ) + j )
        )
        =
        (
          NTP4VCPelts B ( ( NTP4VCOffset B ) + j )
        )
      )
  ) $.
$}

ntp4vc-address-valid-definition $a |- (
  NTP4VCAddressValid A B
) <-> (
  ( NTP4VCMin A )
  <_
  (
    ( NTP4VCOffset A )
    +
    ( NTP4VCSigned32 B )
  )
  /\
  (
    ( NTP4VCOffset A )
    +
    ( NTP4VCSigned32 B )
  )
  <
  ( NTP4VCMax A )
) $.

ntp4vc-continue-definition $a |- (
  NTP4VCContinue A B C D E
) <-> (
  ( NTP4VCSigned32 E ) < ( NTP4VCSigned32 D )
  /\
  (
    (
      0 <_ ( NTP4VCSigned32 E )
      /\
      ( NTP4VCSigned32 E ) <_ ( NTP4VCSigned32 C )
    )
    /\
    (
      NTP4VCRangeEqual
        A B
        ( NTP4VCSigned32 E )
        ( NTP4VCSigned32 C )
    )
  )
) $.

${
  $d o A B C D E $.

  ntp4vc-limb-decision-definition $a |- (
    NTP4VCLimbDecision A B C D E
  ) <-> (
    A. o e. { 0 , 1 }
      (
        (
          (
            (
              NTP4VCPelts
                A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 E )
                )
            )
            =
            (
              NTP4VCPelts
                B
                (
                  ( NTP4VCOffset B )
                  +
                  ( NTP4VCSigned32 E )
                )
            )
            ->
            o = 1
          )
          /\
          (
            o = 1
            ->
            (
              NTP4VCPelts
                A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 E )
                )
            )
            =
            (
              NTP4VCPelts
                B
                (
                  ( NTP4VCOffset B )
                  +
                  ( NTP4VCSigned32 E )
                )
            )
          )
        )
        ->
        (
          (
            o =/= 1
            ->
            (
              (
                (
                  NTP4VCPelts
                    B
                    (
                      ( NTP4VCOffset B )
                      +
                      ( NTP4VCSigned32 E )
                    )
                )
                <
                (
                  NTP4VCPelts
                    A
                    (
                      ( NTP4VCOffset A )
                      +
                      ( NTP4VCSigned32 E )
                    )
                )
                ->
                1 = ( NTP4VCComparison A B C )
              )
              /\
              (
                -.
                (
                  NTP4VCPelts
                    B
                    (
                      ( NTP4VCOffset B )
                      +
                      ( NTP4VCSigned32 E )
                    )
                )
                <
                (
                  NTP4VCPelts
                    A
                    (
                      ( NTP4VCOffset A )
                      +
                      ( NTP4VCSigned32 E )
                    )
                )
                ->
                ( -u 1 ) = ( NTP4VCComparison A B C )
              )
            )
          )
          /\
          (
            o = 1
            ->
            ( NTP4VCContinue A B C D E )
          )
        )
      )
  ) $.
$}

${
  $d o A B C D $.

  ntp4vc-decrement-definition $a |- (
    NTP4VCDecrement A B C D
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) - 1 )
    )
    /\
    A. o e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 o
        )
        =
        (
          ( NTP4VCSigned32 D ) - 1
        )
        ->
        (
          ( NTP4VCAddressValid A o )
          /\
          (
            ( NTP4VCAddressValid B o )
            /\
            ( NTP4VCLimbDecision A B C D o )
          )
        )
      )
  ) $.
$}

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C D
) <-> (
  (
    0 <_ ( NTP4VCSigned32 D )
    /\
    ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 C )
  )
  /\
  (
    NTP4VCRangeEqual
      A B
      ( NTP4VCSigned32 D )
      ( NTP4VCSigned32 C )
  )
) $.

ntp4vc-loop-step-definition $a |- (
  NTP4VCLoopStep A B C D
) <-> (
  (
    NTP4VCLoopInvariant A B C D
  )
  ->
  (
    (
      1 <_ ( NTP4VCSigned32 D )
      ->
      ( NTP4VCDecrement A B C D )
    )
    /\
    (
      -. 1 <_ ( NTP4VCSigned32 D )
      ->
      0 = ( NTP4VCComparison A B C )
    )
  )
) $.

${
  $d i A B C Z $.

  $( Source parameters: A=x, C=sz, B=y, with common zone carrier Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-pointer $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-size-word32 $e |- C e. NTP4VCWord32 $.
  ntp4vc-y-pointer $e |- B e. ( NTP4VCPtr Z ) $.
  ntp4vc-x-valid $e |- (
    NTP4VCValid A ( NTP4VCSigned32 C )
  ) $.
  ntp4vc-y-valid $e |- (
    NTP4VCValid B ( NTP4VCSigned32 C )
  ) $.

  ntp4vc-pearl-multiprecision-compare-wmpn-cmp-vc $a |- (
    0 <_ ( NTP4VCSigned32 C )
    /\
    (
      ( NTP4VCSigned32 C ) <_ ( NTP4VCSigned32 C )
      /\
      (
        (
          NTP4VCRangeEqual
            A B
            ( NTP4VCSigned32 C )
            ( NTP4VCSigned32 C )
        )
        /\
        A. i e. NTP4VCWord32
          ( NTP4VCLoopStep A B C i )
      )
    )
  ) $.
$}
