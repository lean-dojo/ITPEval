$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_cutpointsqtvc: the monotonic-segment
  cutpoint verification condition initializes and preserves cutpoint bounds,
  segment monotonicity, endpoint, ordering, and loop-variant obligations for
  a nonempty integer array. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer arrays and lists. NTP4VCToNat
  and NTP4VCAt reproduce the exported Int.toNat and totalized list lookup with
  default zero. NTP4VCReverse is exact finite-list reversal.

  The source record type list_seq has fields list and seq, the invariant
  seq = reverse list, and extensional equality by those fields. It is
  therefore represented bijectively by Word ZZ itself: a word is the list
  field and NTP4VCReverse of that word is the seq field. The empty word is
  nil, and NTP4VCCons is source list cons. This retains every list_seq value
  and introduces no extra value.

  NTP4VCBool is the exact two-element Boolean carrier. NTP4VCBoolLt and
  NTP4VCEqb are the source comparison-to-Boolean and Boolean equivalence
  functions. NTP4VCMonotone is the source disjunction saying that a half-open
  array segment is either strictly increasing or nonincreasing.

  The remaining predicates factor the original nested verification condition.
  Expanding their biconditional definitions recovers every source integer,
  Boolean, array, and list_seq quantifier; every bound and loop-variant
  premise; both nested conditionals; and every conjunct of the final
  cutpoint specification. Source let-bindings are replaced by direct
  substitution, and proposition-valued conditionals are represented by
  equivalent exhaustive guarded implications. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCBool NTP4VCFalse NTP4VCTrue
  NTP4VCToNat NTP4VCAt NTP4VCReverse NTP4VCCons
  NTP4VCSeqAt NTP4VCLast NTP4VCBoolLt NTP4VCEqb
  NTP4VCMonotone NTP4VCBounds NTP4VCSegments NTP4VCOrdered
  NTP4VCCore NTP4VCInitial NTP4VCLoopInvariant NTP4VCFinal
  NTP4VCYBounds NTP4VCBoolGuard NTP4VCSameDirection
  NTP4VCNewCut NTP4VCBoolStep NTP4VCGrowY NTP4VCOuterThen
  NTP4VCExtendFinal NTP4VCOuterStep NTP4VCCutpointsVC
$.

ntp4vc-bool-syntax $a class NTP4VCBool $.
ntp4vc-false-syntax $a class NTP4VCFalse $.
ntp4vc-true-syntax $a class NTP4VCTrue $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-reverse-syntax $a class ( NTP4VCReverse A ) $.
ntp4vc-cons-syntax $a class ( NTP4VCCons A B ) $.
ntp4vc-seq-at-syntax $a class ( NTP4VCSeqAt A B ) $.
ntp4vc-last-syntax $a class ( NTP4VCLast A ) $.
ntp4vc-bool-lt-syntax $a class ( NTP4VCBoolLt A B ) $.
ntp4vc-eqb-syntax $a class ( NTP4VCEqb A B ) $.

ntp4vc-monotone-syntax
  $a wff ( NTP4VCMonotone A B C ) $.
ntp4vc-bounds-syntax
  $a wff ( NTP4VCBounds A B ) $.
ntp4vc-segments-syntax
  $a wff ( NTP4VCSegments A B ) $.
ntp4vc-ordered-syntax
  $a wff ( NTP4VCOrdered A ) $.
ntp4vc-core-syntax
  $a wff ( NTP4VCCore A B C ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C ) $.
ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B ) $.
ntp4vc-y-bounds-syntax
  $a wff ( NTP4VCYBounds A B ) $.
ntp4vc-bool-guard-syntax
  $a wff ( NTP4VCBoolGuard A B C D E ) $.
ntp4vc-same-direction-syntax
  $a wff ( NTP4VCSameDirection A B C D ) $.
ntp4vc-new-cut-syntax
  $a wff ( NTP4VCNewCut A B C D ) $.
ntp4vc-bool-step-syntax
  $a wff ( NTP4VCBoolStep A B C D E ) $.
ntp4vc-grow-y-syntax
  $a wff ( NTP4VCGrowY A B C D ) $.
ntp4vc-outer-then-syntax
  $a wff ( NTP4VCOuterThen A B C ) $.
ntp4vc-extend-final-syntax
  $a wff ( NTP4VCExtendFinal A B C ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C ) $.
ntp4vc-cutpoints-vc-syntax
  $a wff ( NTP4VCCutpointsVC A ) $.

ntp4vc-bool-definition $a |-
  NTP4VCBool = ( 0 ..^ 2 ) $.
ntp4vc-false-definition $a |-
  NTP4VCFalse = 0 $.
ntp4vc-true-definition $a |-
  NTP4VCTrue = 1 $.

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

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

ntp4vc-cons-definition $a |- (
  NTP4VCCons A B
) = (
  <" A "> ++ B
) $.

ntp4vc-seq-at-definition $a |- (
  NTP4VCSeqAt A B
) = (
  NTP4VCAt ( NTP4VCReverse A ) B
) $.

ntp4vc-last-definition $a |- (
  NTP4VCLast A
) = (
  NTP4VCSeqAt A ( ( # ` A ) - 1 )
) $.

ntp4vc-bool-lt-definition $a |- (
  NTP4VCBoolLt A B
) = if (
  A < B ,
  NTP4VCTrue ,
  NTP4VCFalse
) $.

ntp4vc-eqb-definition $a |- (
  NTP4VCEqb A B
) = if (
  A = B ,
  NTP4VCTrue ,
  NTP4VCFalse
) $.

${
  $d x y A B C $.

  ntp4vc-monotone-definition $a |- (
    NTP4VCMonotone A B C
  ) <->
  (
    A. x e. ZZ A. y e. ZZ
      (
        (
          B <_ x
          /\
          (
            x < y
            /\
            y < C
          )
        )
        ->
        ( NTP4VCAt A x ) < ( NTP4VCAt A y )
      )
    \/
    A. x e. ZZ A. y e. ZZ
      (
        (
          B <_ x
          /\
          (
            x < y
            /\
            y < C
          )
        )
        ->
        ( NTP4VCAt A y ) <_ ( NTP4VCAt A x )
      )
  ) $.
$}

${
  $d z A B $.

  ntp4vc-bounds-definition $a |- (
    NTP4VCBounds A B
  ) <->
  A. z e. ran A
    (
      0 <_ z
      /\
      z <_ B
    ) $.
$}

${
  $d k A B $.

  ntp4vc-segments-definition $a |- (
    NTP4VCSegments A B
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < ( ( # ` B ) - 1 )
      )
      ->
      (
        NTP4VCMonotone
          A
          ( NTP4VCSeqAt B k )
          ( NTP4VCSeqAt B ( k + 1 ) )
      )
    ) $.
$}

${
  $d i j A $.

  ntp4vc-ordered-definition $a |- (
    NTP4VCOrdered A
  ) <->
  A. i e. ZZ A. j e. ZZ
    (
      (
        0 <_ i
        /\
        (
          i < j
          /\
          j < ( # ` A )
        )
      )
      ->
      ( NTP4VCSeqAt A i ) <_ ( NTP4VCSeqAt A j )
    ) $.
$}

ntp4vc-core-definition $a |- (
  NTP4VCCore A B C
) <->
(
  0 < ( # ` B )
  /\
  (
    ( NTP4VCSeqAt B 0 ) = 0
    /\
    (
      ( NTP4VCBounds B C )
      /\
      (
        ( NTP4VCSegments A B )
        /\
        ( NTP4VCOrdered B )
      )
    )
  )
) $.

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C
) <->
(
  1 = ( 0 + 1 )
  /\
  (
    (
      0 < 1
      /\
      1 <_ ( C + 1 )
    )
    /\
    (
      ( NTP4VCCore A B C )
      /\
      ( NTP4VCLast B ) = 0
    )
  )
) $.

ntp4vc-loop-invariant-definition $a |- (
  NTP4VCLoopInvariant A B C
) <->
(
  (
    0 < ( ( NTP4VCLast B ) + 1 )
    /\
    ( ( NTP4VCLast B ) + 1 ) <_ ( C + 1 )
  )
  /\
  ( NTP4VCCore A B C )
) $.

ntp4vc-final-definition $a |- (
  NTP4VCFinal A B
) <->
(
  ( NTP4VCCore A B ( # ` A ) )
  /\
  (
    ( NTP4VCLast B ) = ( # ` A )
    /\
    2 <_ ( # ` B )
  )
) $.

ntp4vc-y-bounds-definition $a |- (
  NTP4VCYBounds A B
) <->
(
  (
    0 <_ B
    /\
    B < ( # ` A )
  )
  /\
  (
    0 <_ ( B - 1 )
    /\
    ( B - 1 ) < ( # ` A )
  )
) $.

ntp4vc-bool-guard-definition $a |- (
  NTP4VCBoolGuard A B C D E
) <->
(
  (
    C < E
    ->
    (
      D
      =
      (
        NTP4VCEqb
          ( NTP4VCBoolLt
            ( NTP4VCAt A ( C - 1 ) )
            ( NTP4VCAt A C )
          )
          ( NTP4VCBoolLt
            ( NTP4VCAt A ( NTP4VCLast B ) )
            ( NTP4VCAt A ( ( NTP4VCLast B ) + 1 ) )
          )
      )
      /\
      (
        D = NTP4VCTrue
        <->
        (
          NTP4VCBoolLt
            ( NTP4VCAt A ( C - 1 ) )
            ( NTP4VCAt A C )
        )
        =
        (
          NTP4VCBoolLt
            ( NTP4VCAt A ( NTP4VCLast B ) )
            ( NTP4VCAt A ( ( NTP4VCLast B ) + 1 ) )
        )
      )
    )
  )
  /\
  (
    E <_ C
    ->
    D = NTP4VCFalse
  )
) $.

ntp4vc-same-direction-definition $a |- (
  NTP4VCSameDirection A B C D
) <->
(
  (
    0 <_ ( D - C )
    /\
    ( D - ( C + 1 ) ) < ( D - C )
  )
  /\
  (
    (
      ( ( NTP4VCLast B ) + 1 ) <_ ( C + 1 )
      /\
      ( C + 1 ) <_ D
    )
    /\
    (
      NTP4VCMonotone
        A
        ( NTP4VCLast B )
        ( C + 1 )
    )
  )
) $.

${
  $d x A B C D $.

  ntp4vc-new-cut-definition $a |- (
    NTP4VCNewCut A B C D
  ) <->
  A. x e. Word ZZ
    (
      x = ( NTP4VCCons C B )
      ->
      (
        (
          0 <_ ( D - ( ( NTP4VCLast B ) + 1 ) )
          /\
          (
            D - ( C + 1 )
          )
          <
          (
            D - ( ( NTP4VCLast B ) + 1 )
          )
        )
        /\
        (
          (
            0 < ( C + 1 )
            /\
            ( C + 1 ) <_ ( D + 1 )
          )
          /\
          (
            ( NTP4VCCore A x D )
            /\
            ( NTP4VCLast x ) = C
          )
        )
      )
    ) $.
$}

ntp4vc-bool-step-definition $a |- (
  NTP4VCBoolStep A B C D E
) <->
(
  (
    D = NTP4VCTrue
    ->
    ( NTP4VCSameDirection A B C E )
  )
  /\
  (
    D = NTP4VCFalse
    ->
    ( NTP4VCNewCut A B C E )
  )
) $.

${
  $d b A B C D $.

  ntp4vc-grow-y-definition $a |- (
    NTP4VCGrowY A B C D
  ) <->
  (
    (
      (
        ( ( NTP4VCLast B ) + 1 ) <_ C
        /\
        C <_ D
      )
      /\
      (
        NTP4VCMonotone
          A
          ( NTP4VCLast B )
          C
      )
    )
    ->
    (
      (
        C < D
        ->
        ( NTP4VCYBounds A C )
      )
      /\
      A. b e. NTP4VCBool
        (
          ( NTP4VCBoolGuard A B C b D )
          ->
          ( NTP4VCBoolStep A B C b D )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  ntp4vc-outer-then-definition $a |- (
    NTP4VCOuterThen A B C
  ) <->
  (
    (
      (
        0 <_ ( ( NTP4VCLast B ) + 1 )
        /\
        ( ( NTP4VCLast B ) + 1 ) < ( # ` A )
      )
      /\
      (
        0 <_ ( NTP4VCLast B )
        /\
        ( NTP4VCLast B ) < ( # ` A )
      )
    )
    /\
    (
      (
        (
          ( ( NTP4VCLast B ) + 1 )
          <_
          ( ( NTP4VCLast B ) + 1 )
          /\
          ( ( NTP4VCLast B ) + 1 ) <_ C
        )
        /\
        (
          NTP4VCMonotone
            A
            ( NTP4VCLast B )
            ( ( NTP4VCLast B ) + 1 )
        )
      )
      /\
      A. y e. ZZ
        ( NTP4VCGrowY A B y C )
    )
  ) $.
$}

${
  $d x A B C $.

  ntp4vc-extend-final-definition $a |- (
    NTP4VCExtendFinal A B C
  ) <->
  A. x e. Word ZZ
    (
      x = ( NTP4VCCons C B )
      ->
      ( NTP4VCFinal A x )
    ) $.
$}

ntp4vc-outer-step-definition $a |- (
  NTP4VCOuterStep A B C
) <->
(
  (
    ( ( NTP4VCLast B ) + 1 ) < C
    ->
    ( NTP4VCOuterThen A B C )
  )
  /\
  (
    C <_ ( ( NTP4VCLast B ) + 1 )
    ->
    (
      (
        ( NTP4VCLast B ) < C
        ->
        ( NTP4VCExtendFinal A B C )
      )
      /\
      (
        C <_ ( NTP4VCLast B )
        ->
        ( NTP4VCFinal A B )
      )
    )
  )
) $.

${
  $d x y A $.

  ntp4vc-cutpoints-vc-definition $a |- (
    NTP4VCCutpointsVC A
  ) <->
  A. x e. Word ZZ
    (
      x = ( NTP4VCCons 0 (/) )
      ->
      (
        ( NTP4VCInitial A x ( # ` A ) )
        /\
        A. y e. Word ZZ
          (
            ( NTP4VCLoopInvariant A y ( # ` A ) )
            ->
            ( NTP4VCOuterStep A y ( # ` A ) )
          )
      )
    ) $.
$}

${
  ntp4vc-array $e |- A e. Word ZZ $.
  ntp4vc-array-nonempty $e |- 0 < ( # ` A ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-top-cutpoints-vc
    $a |- ( NTP4VCCutpointsVC A ) $.
$}
