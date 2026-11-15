$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_updateqtvc: the cumulative-array point-update
  verification condition preserves the loop invariants, restores all prefix
  sums, and records the updated-cell and frame postconditions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat
  reproduces Int.toNat, NTP4VCAt is integer-indexed lookup with default zero
  outside [0, length), and NTP4VCSet, NTP4VCNth, and NTP4VCFunUpdate
  reproduce List.set, integer-indexed lookup, and Function.update.

  NTP4VCSum is the finite sum over a half-open interval; under every bound in
  this VC it is definitionally equivalent to the source ArraySum.sum.
  NTP4VCCumulative directly expands is_cumulative_array_for. The suffix,
  prefix, update, loop-step, loop-exit, and postcondition predicates are
  biconditional factorizations of the corresponding source subformulas.

  Expanding all definitions recovers the original integer and list domains,
  assumptions, nested update implications, universal quantifiers over loop
  indices and intermediate arrays, both loop-range branches, and the complete
  final frame property. The final declaration is Metamath's native unproved
  $a statement encoding; every preceding $a is syntax or a faithful
  definition required to state it, and this database contains no $p proof
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate
  NTP4VCSum NTP4VCCumulative NTP4VCSetFunction
  NTP4VCSuffix NTP4VCPrefix NTP4VCOther NTP4VCPost
  NTP4VCLoopStep NTP4VCLoopPremise NTP4VCAllLoopIndices
  NTP4VCLoopExit NTP4VCIntermediate NTP4VCAllIntermediate
  NTP4VCLoopContinuation
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-nth-syntax
  $a class ( NTP4VCNth A ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C ) $.
ntp4vc-sum-syntax
  $a class ( NTP4VCSum A B C ) $.

ntp4vc-cumulative-syntax
  $a wff ( NTP4VCCumulative A B ) $.
ntp4vc-set-function-syntax
  $a wff ( NTP4VCSetFunction A B C ) $.
ntp4vc-suffix-syntax
  $a wff ( NTP4VCSuffix A B C D ) $.
ntp4vc-prefix-syntax
  $a wff ( NTP4VCPrefix A B C ) $.
ntp4vc-other-syntax
  $a wff ( NTP4VCOther A B C ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D E ) $.
ntp4vc-loop-step-syntax
  $a wff ( NTP4VCLoopStep A B C D ) $.
ntp4vc-loop-premise-syntax
  $a wff ( NTP4VCLoopPremise A B C D E F ) $.
ntp4vc-all-loop-indices-syntax
  $a wff ( NTP4VCAllLoopIndices A B C D E ) $.
ntp4vc-loop-exit-syntax
  $a wff ( NTP4VCLoopExit A B C D E F G ) $.
ntp4vc-intermediate-syntax
  $a wff ( NTP4VCIntermediate A B C D E F G H ) $.
ntp4vc-all-intermediate-syntax
  $a wff ( NTP4VCAllIntermediate A B C D E F G H ) $.
ntp4vc-loop-continuation-syntax
  $a wff ( NTP4VCLoopContinuation A B C D E F ) $.

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
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A $.

  ntp4vc-nth-definition $a |- (
    NTP4VCNth A
  ) = (
    k e. ZZ |->
      ( NTP4VCAt A k )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C
  ) = (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A B C
  ) = sum_ k e.
    (
      ( NTP4VCToNat B )
      ..^
      ( NTP4VCToNat C )
    )
    ( NTP4VCAt A k ) $.
$}

${
  $d k A B $.

  ntp4vc-cumulative-definition $a |- (
    NTP4VCCumulative A B
  ) <->
  (
    ( # ` A ) = ( ( # ` B ) + 1 )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        ->
        ( NTP4VCAt A k ) = ( NTP4VCSum B 0 k )
      )
  ) $.
$}

ntp4vc-set-function-definition $a |- (
  NTP4VCSetFunction A B C
) <->
(
  ( NTP4VCNth ( NTP4VCSet A B C ) )
  =
  (
    NTP4VCFunUpdate
      ( NTP4VCNth A )
      B
      C
  )
) $.

${
  $d k A B C D $.

  ntp4vc-suffix-definition $a |- (
    NTP4VCSuffix A B C D
  ) <->
  A. k e. ZZ
    (
      (
        C <_ k
        /\
        k < ( # ` A )
      )
      ->
      ( NTP4VCAt A k )
      =
      (
        ( NTP4VCSum B 0 k )
        -
        D
      )
    ) $.
$}

${
  $d k A B C $.

  ntp4vc-prefix-definition $a |- (
    NTP4VCPrefix A B C
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < C
      )
      ->
      ( NTP4VCAt A k ) = ( NTP4VCSum B 0 k )
    ) $.
$}

${
  $d k A B C $.

  ntp4vc-other-definition $a |- (
    NTP4VCOther A B C
  ) <->
  A. k e. ZZ
    (
      (
        (
          0 <_ k
          /\
          k < ( # ` A )
        )
        /\
        -. k = C
      )
      ->
      ( NTP4VCAt A k ) = ( NTP4VCAt B k )
    ) $.
$}

ntp4vc-post-definition $a |- (
  NTP4VCPost A B C D E
) <->
(
  ( NTP4VCCumulative A B )
  /\
  (
    ( NTP4VCAt B D ) = E
    /\
    ( NTP4VCOther B C D )
  )
) $.

ntp4vc-loop-step-definition $a |- (
  NTP4VCLoopStep A B C D
) <->
(
  (
    0 <_ C
    /\
    C < ( # ` A )
  )
  /\
  (
    (
      0 <_ C
      /\
      C < ( # ` A )
    )
    /\
    (
      (
        #
        `
        (
          NTP4VCSet
            A
            C
            ( ( NTP4VCAt A C ) + D )
        )
      )
      =
      ( # ` A )
      ->
      (
        (
          NTP4VCSetFunction
            A
            C
            ( ( NTP4VCAt A C ) + D )
        )
        ->
        (
          (
            NTP4VCSuffix
              (
                NTP4VCSet
                  A
                  C
                  ( ( NTP4VCAt A C ) + D )
              )
              B
              ( C + 1 )
              D
          )
          /\
          (
            NTP4VCPrefix
              (
                NTP4VCSet
                  A
                  C
                  ( ( NTP4VCAt A C ) + D )
              )
              B
              ( C + 1 )
          )
        )
      )
    )
  )
) $.

ntp4vc-loop-premise-definition $a |- (
  NTP4VCLoopPremise A B C D E F
) <->
(
  (
    E <_ C
    /\
    C <_ D
  )
  /\
  (
    ( NTP4VCSuffix A B C F )
    /\
    ( NTP4VCPrefix A B C )
  )
) $.

${
  $d j A B C D E $.

  ntp4vc-all-loop-indices-definition $a |- (
    NTP4VCAllLoopIndices A B C D E
  ) <->
  A. j e. ZZ
    (
      ( NTP4VCLoopPremise A B j C D E )
      ->
      ( NTP4VCLoopStep A B j E )
    ) $.
$}

ntp4vc-loop-exit-definition $a |- (
  NTP4VCLoopExit A B C D E F G
) <->
(
  (
    ( NTP4VCSuffix A B ( F + 1 ) G )
    /\
    ( NTP4VCPrefix A B ( F + 1 ) )
  )
  ->
  ( NTP4VCPost A B C D E )
) $.

ntp4vc-intermediate-definition $a |- (
  NTP4VCIntermediate A B C D E F G H
) <->
(
  ( NTP4VCAllLoopIndices A B F G H )
  /\
  ( NTP4VCLoopExit A B C D E F H )
) $.

${
  $d x A B C D E F G H $.

  ntp4vc-all-intermediate-definition $a |- (
    NTP4VCAllIntermediate A B C D E F G H
  ) <->
  A. x e. Word ZZ
    (
      ( # ` x ) = ( # ` A )
      ->
      ( NTP4VCIntermediate x B C D E F G H )
    ) $.
$}

ntp4vc-loop-continuation-definition $a |- (
  NTP4VCLoopContinuation A B C D E F
) <->
(
  (
    ( D + 1 )
    <_
    ( ( ( # ` A ) - 1 ) + 1 )
    ->
    (
      (
        ( NTP4VCSuffix A B ( D + 1 ) F )
        /\
        ( NTP4VCPrefix A B ( D + 1 ) )
      )
      /\
      (
        NTP4VCAllIntermediate
          A
          B
          C
          D
          E
          ( ( # ` A ) - 1 )
          ( D + 1 )
          F
      )
    )
  )
  /\
  (
    ( ( ( # ` A ) - 1 ) + 1 )
    <
    ( D + 1 )
    ->
    ( NTP4VCPost A B C D E )
  )
) $.

${
  $( Source parameters: A=c, B=a, C=i, and D=v. $)

  ntp4vc-c-list $e |- A e. Word ZZ $.
  ntp4vc-a-list $e |- B e. Word ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-v-integer $e |- D e. ZZ $.

  ntp4vc-cumulative-array $e |- ( NTP4VCCumulative A B ) $.
  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i-below-a-length $e |- C < ( # ` B ) $.

  ntp4vc-pearl-sumrange-cumulative-array-update-vc $a |- (
    0 <_ C
    /\
    (
      C < ( # ` A )
      /\
      (
        (
          0 <_ ( C + 1 )
          /\
          ( C + 1 ) < ( # ` A )
        )
        /\
        (
          (
            0 <_ C
            /\
            C < ( # ` B )
          )
          /\
          (
            (
              #
              `
              ( NTP4VCSet B C D )
            )
            =
            ( # ` B )
            ->
            (
              ( NTP4VCSetFunction B C D )
              ->
              (
                NTP4VCLoopContinuation
                  A
                  ( NTP4VCSet B C D )
                  B
                  C
                  D
                  (
                    (
                      D
                      -
                      ( NTP4VCAt A ( C + 1 ) )
                    )
                    +
                    ( NTP4VCAt A C )
                  )
              )
            )
          )
        )
      )
    )
  ) $.
$}
