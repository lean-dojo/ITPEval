$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/decrease1_Decrease1_searchqtvc: the integer-list search verification
  condition maintains the absence of earlier zero entries, preserves progress
  when advancing by a positive entry or by one, and specifies either a
  first-zero result or exhaustion of the list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source conversion from integers to naturals, and NTP4VCAt is the source
  totalized list lookup with integer default 0.

  NTP4VCDecrease1 directly expands the source adjacent-step assumption.
  NTP4VCInvariant retains the source's nested length guard, while
  NTP4VCNoZeroBefore represents the unguarded first-zero and exhaustion
  postconditions. NTP4VCPositiveStep and NTP4VCNonpositiveStep preserve the
  two variant-decrease obligations and the corresponding next-index
  invariant. NTP4VCInsideCase and NTP4VCSearchCase render proposition-valued
  source conditionals as exhaustive guarded disjunctions. Splitting the typed
  list parameter and theorem assumption into scoped essential hypotheses is
  bidirectionally equivalent to the source curried theorem. Every integer and
  word quantifier retains its full source domain. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCInBounds NTP4VCDecrease1
  NTP4VCInvariant NTP4VCNoZeroBefore
  NTP4VCPositiveStep NTP4VCNonpositiveStep
  NTP4VCInsideCase NTP4VCOutsideCase NTP4VCSearchCase
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-in-bounds-syntax
  $a wff ( NTP4VCInBounds A B ) $.
ntp4vc-decrease1-syntax
  $a wff ( NTP4VCDecrease1 A ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B ) $.
ntp4vc-no-zero-before-syntax
  $a wff ( NTP4VCNoZeroBefore A B ) $.
ntp4vc-positive-step-syntax
  $a wff ( NTP4VCPositiveStep A B ) $.
ntp4vc-nonpositive-step-syntax
  $a wff ( NTP4VCNonpositiveStep A B ) $.
ntp4vc-inside-case-syntax
  $a wff ( NTP4VCInsideCase A B ) $.
ntp4vc-outside-case-syntax
  $a wff ( NTP4VCOutsideCase A ) $.
ntp4vc-search-case-syntax
  $a wff ( NTP4VCSearchCase A B ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-in-bounds-definition $a |- (
  ( NTP4VCInBounds A B )
  <->
  (
    0 <_ B
    /\
    B < ( # ` A )
  )
) $.

${
  $d j A $.

  ntp4vc-decrease1-definition $a |- (
    ( NTP4VCDecrease1 A )
    <->
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < ( ( # ` A ) - 1 )
        )
        ->
        (
          ( ( NTP4VCAt A j ) - 1 )
          <_
          ( NTP4VCAt A ( j + 1 ) )
        )
      )
  ) $.
$}

${
  $d j A B $.

  ntp4vc-invariant-definition $a |- (
    ( NTP4VCInvariant A B )
    <->
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < B
        )
        ->
        (
          j < ( # ` A )
          ->
          ( NTP4VCAt A j ) =/= 0
        )
      )
  ) $.
$}

${
  $d j A B $.

  ntp4vc-no-zero-before-definition $a |- (
    ( NTP4VCNoZeroBefore A B )
    <->
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < B
        )
        ->
        ( NTP4VCAt A j ) =/= 0
      )
  ) $.
$}

ntp4vc-positive-step-definition $a |- (
  ( NTP4VCPositiveStep A B )
  <->
  (
    ( NTP4VCInBounds A B )
    /\
    (
      (
        0 <_ ( ( # ` A ) - B )
        /\
        (
          ( ( # ` A ) - ( B + ( NTP4VCAt A B ) ) )
          <
          ( ( # ` A ) - B )
        )
      )
      /\
      (
        0 <_ ( B + ( NTP4VCAt A B ) )
        /\
        (
          NTP4VCInvariant
            A ( B + ( NTP4VCAt A B ) )
        )
      )
    )
  )
) $.

ntp4vc-nonpositive-step-definition $a |- (
  ( NTP4VCNonpositiveStep A B )
  <->
  (
    (
      0 <_ ( ( # ` A ) - B )
      /\
      (
        ( ( # ` A ) - ( B + 1 ) )
        <
        ( ( # ` A ) - B )
      )
    )
    /\
    (
      0 <_ ( B + 1 )
      /\
      ( NTP4VCInvariant A ( B + 1 ) )
    )
  )
) $.

ntp4vc-inside-case-definition $a |- (
  ( NTP4VCInsideCase A B )
  <->
  (
    ( NTP4VCInBounds A B )
    /\
    (
      (
        ( NTP4VCAt A B ) = 0
        /\
        (
          (
            B = ( -u 1 )
            /\
            ( NTP4VCNoZeroBefore A ( # ` A ) )
          )
          \/
          (
            ( NTP4VCInBounds A B )
            /\
            (
              ( NTP4VCAt A B ) = 0
              /\
              ( NTP4VCNoZeroBefore A B )
            )
          )
        )
      )
      \/
      (
        ( NTP4VCAt A B ) =/= 0
        /\
        (
          ( NTP4VCInBounds A B )
          /\
          (
            (
              0 < ( NTP4VCAt A B )
              /\
              ( NTP4VCPositiveStep A B )
            )
            \/
            (
              -. 0 < ( NTP4VCAt A B )
              /\
              ( NTP4VCNonpositiveStep A B )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-outside-case-definition $a |- (
  ( NTP4VCOutsideCase A )
  <->
  (
    ( NTP4VCNoZeroBefore A ( # ` A ) )
    \/
    (
      ( NTP4VCInBounds A ( -u 1 ) )
      /\
      (
        ( NTP4VCAt A ( -u 1 ) ) = 0
        /\
        ( NTP4VCNoZeroBefore A ( -u 1 ) )
      )
    )
  )
) $.

ntp4vc-search-case-definition $a |- (
  ( NTP4VCSearchCase A B )
  <->
  (
    (
      B < ( # ` A )
      /\
      ( NTP4VCInsideCase A B )
    )
    \/
    (
      -. B < ( # ` A )
      /\
      ( NTP4VCOutsideCase A )
    )
  )
) $.

${
  $d i A $.

  $( Source parameter: A=a. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-fact0 $e |- ( NTP4VCDecrease1 A ) $.

  ntp4vc-pearl-decrease1-search-vc $a |- (
    0 <_ 0
    /\
    (
      ( NTP4VCInvariant A 0 )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            ( NTP4VCInvariant A i )
          )
          ->
          ( NTP4VCSearchCase A i )
        )
    )
  ) $.
$}
