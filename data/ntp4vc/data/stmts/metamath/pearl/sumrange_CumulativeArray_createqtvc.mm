$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_createqtvc: the cumulative-array creation
  verification condition initializes a zero array, preserves prefix sums
  through each list update, and establishes the cumulative-array
  specification at loop exit. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, NTP4VCNth, and NTP4VCFunUpdate reproduce Int.toNat,
  totalized list lookup with default zero, List.set, the total integer-indexed
  lookup function, and Function.update.

  NTP4VCSum is the finite sum over the indicated half-open interval. At every
  use admitted by the VC's bounds it is definitionally equivalent to the
  recursively specified source ArraySum.sum. NTP4VCCumulative directly
  expands is_cumulative_array_for. The remaining predicates are
  biconditional factorizations of the source zero initialization, prefix-sum
  invariant, nested update implication, loop-preservation obligation, and
  loop-exit condition.

  Expanding these definitions recovers every source list and integer
  quantifier, length equality, bound, implication, let-bound value, updated
  list, extensional function-update premise, and both loop-exit branches.
  The source parameter a is a scoped essential hypothesis, while s and s1
  remain internally quantified over all finite integer lists. The final
  declaration is Metamath's native unproved $a statement encoding; every
  preceding $a is syntax or a faithful definition required to state it, and
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate
  NTP4VCSum NTP4VCCumulative NTP4VCZeroInit NTP4VCPrefix
  NTP4VCUpdateLaw NTP4VCStep NTP4VCLoop
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
ntp4vc-zero-init-syntax
  $a wff ( NTP4VCZeroInit A B ) $.
ntp4vc-prefix-syntax
  $a wff ( NTP4VCPrefix A B C ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D ) $.

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
  $d i A B $.

  ntp4vc-cumulative-definition $a |- (
    NTP4VCCumulative A B
  ) <->
  (
    ( # ` A ) = ( ( # ` B ) + 1 )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        ( NTP4VCAt A i ) = ( NTP4VCSum B 0 i )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-zero-init-definition $a |- (
    NTP4VCZeroInit A B
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < B
      )
      ->
      ( NTP4VCAt A i ) = 0
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

ntp4vc-update-law-definition $a |- (
  NTP4VCUpdateLaw A B C D
) <->
(
  ( # ` ( NTP4VCSet A B C ) ) = ( # ` A )
  ->
  (
    ( NTP4VCNth ( NTP4VCSet A B C ) )
    =
    (
      NTP4VCFunUpdate
        ( NTP4VCNth A )
        B
        C
    )
    ->
    (
      NTP4VCPrefix
        ( NTP4VCSet A B C )
        D
        ( B + 1 )
    )
  )
) $.

ntp4vc-step-definition $a |- (
  NTP4VCStep A B C
) <->
(
  (
    0 <_ ( C - 1 )
    /\
    ( C - 1 ) < ( # ` B )
  )
  /\
  (
    (
      0 <_ ( C - 1 )
      /\
      ( C - 1 ) < ( # ` A )
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
        NTP4VCUpdateLaw
          A
          C
          (
            ( NTP4VCAt A ( C - 1 ) )
            +
            ( NTP4VCAt B ( C - 1 ) )
          )
          B
      )
    )
  )
) $.

${
  $d i A B C D $.

  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D
  ) <->
  (
    ( # ` A ) = ( # ` B )
    ->
    (
      A. i e. ZZ
        (
          (
            (
              1 <_ i
              /\
              i <_ D
            )
            /\
            ( NTP4VCPrefix A C i )
          )
          ->
          ( NTP4VCStep A C i )
        )
      /\
      (
        ( NTP4VCPrefix A C ( D + 1 ) )
        ->
        ( NTP4VCCumulative A C )
      )
    )
  ) $.
$}

${
  $d i k s t A $.

  $( Source theorem parameter A=a; bound variables s and t are s and s1. $)
  ntp4vc-a-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-sumrange-cumulative-array-create-vc $a |- (
    0 <_ ( ( # ` A ) + 1 )
    /\
    A. s e. Word ZZ
      (
        (
          ( NTP4VCZeroInit s ( ( # ` A ) + 1 ) )
          /\
          ( # ` s ) = ( ( # ` A ) + 1 )
        )
        ->
        (
          (
            1 <_ ( ( # ` A ) + 1 )
            ->
            (
              ( NTP4VCPrefix s A 1 )
              /\
              A. t e. Word ZZ
                (
                  NTP4VCLoop
                    t
                    s
                    A
                    ( # ` A )
                )
            )
          )
          /\
          (
            ( ( # ` A ) + 1 ) < 1
            ->
            ( NTP4VCCumulative s A )
          )
        )
      )
  ) $.
$}
