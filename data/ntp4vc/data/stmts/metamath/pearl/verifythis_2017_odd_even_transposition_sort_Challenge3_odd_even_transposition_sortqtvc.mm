$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_transposition_sort_Challenge3_odd_even_transposition_sortqtvc:
  the sequential odd-even transposition-sort verification condition preserves
  permutation and alternating local-order invariants while adjacent swaps
  decrease the inversion count, culminating in a sorted permutation. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer arrays are represented exactly by arbitrary finite SetMM words over
  ZZ. NTP4VCToNat, NTP4VCAt, and NTP4VCSet reproduce the exported integer to
  natural conversion, totalized lookup with integer default zero, and list
  update. NTP4VCPerm compares every integer multiplicity and is equivalent in
  both directions to finite-list permutation. NTP4VCExchange defines the
  second word as the first word with the selected entries swapped, matching
  the primary Why3 ArraySwap semantics.

  NTP4VCInversions is the source inversion count: for each index i it counts
  later indices j whose value is smaller, then sums over all i. This is
  definitionally the exported nested half-open numof and sum construction.
  NTP4VCSorted, NTP4VCOddSorted, and NTP4VCEvenSorted retain their full
  integer-indexed source quantifiers.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every source
  integer, Boolean, and intermediate-array quantifier; every length premise,
  implication, loop invariant, adjacent-exchange continuation, inversion
  comparison, lexicographic variant obligation, and final conclusion.
  Let-bound indices are replaced by direct substitution, and proposition
  conditionals are represented by equivalent exhaustive guarded disjunctions.
  Booleans use the exact two-element carrier, and no arbitrary domain is
  bounded or otherwise narrowed. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCBool NTP4VCFalse NTP4VCTrue NTP4VCBoolCost
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCInversions
  NTP4VCPerm NTP4VCExchange NTP4VCSorted
  NTP4VCOddSorted NTP4VCEvenSorted NTP4VCInvRel
  NTP4VCOddInvariant NTP4VCOddAfterSwap NTP4VCOddNoSwap
  NTP4VCOddSwap NTP4VCOddStep NTP4VCOddInitial
  NTP4VCEvenInitial NTP4VCEvenInvariant
  NTP4VCEvenAfterSwap NTP4VCEvenNoSwap NTP4VCEvenSwap
  NTP4VCEvenExit NTP4VCEvenStep NTP4VCEvenLoop
  NTP4VCOddLoop NTP4VCOuterBranch NTP4VCOddEvenVC
$.

ntp4vc-bool-syntax $a class NTP4VCBool $.
ntp4vc-false-syntax $a class NTP4VCFalse $.
ntp4vc-true-syntax $a class NTP4VCTrue $.
ntp4vc-bool-cost-syntax $a class ( NTP4VCBoolCost A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-inversions-syntax $a class ( NTP4VCInversions A ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-exchange-syntax $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A ) $.
ntp4vc-odd-sorted-syntax $a wff ( NTP4VCOddSorted A B ) $.
ntp4vc-even-sorted-syntax $a wff ( NTP4VCEvenSorted A B ) $.
ntp4vc-inv-rel-syntax $a wff ( NTP4VCInvRel A B C ) $.

ntp4vc-odd-invariant-syntax
  $a wff ( NTP4VCOddInvariant A B C D E ) $.
ntp4vc-odd-after-swap-syntax
  $a wff ( NTP4VCOddAfterSwap A B C D E ) $.
ntp4vc-odd-no-swap-syntax
  $a wff ( NTP4VCOddNoSwap A B C D E ) $.
ntp4vc-odd-swap-syntax
  $a wff ( NTP4VCOddSwap A B C D ) $.
ntp4vc-odd-step-syntax
  $a wff ( NTP4VCOddStep A B C D E F ) $.
ntp4vc-odd-initial-syntax
  $a wff ( NTP4VCOddInitial A B ) $.

ntp4vc-even-initial-syntax
  $a wff ( NTP4VCEvenInitial A B C D ) $.
ntp4vc-even-invariant-syntax
  $a wff ( NTP4VCEvenInvariant A B C D E ) $.
ntp4vc-even-after-swap-syntax
  $a wff ( NTP4VCEvenAfterSwap A B C D E ) $.
ntp4vc-even-no-swap-syntax
  $a wff ( NTP4VCEvenNoSwap A B C D E ) $.
ntp4vc-even-swap-syntax
  $a wff ( NTP4VCEvenSwap A B C D ) $.
ntp4vc-even-exit-syntax
  $a wff ( NTP4VCEvenExit A B C D E ) $.
ntp4vc-even-step-syntax
  $a wff ( NTP4VCEvenStep A B C D E F ) $.
ntp4vc-even-loop-syntax
  $a wff ( NTP4VCEvenLoop A B C D E ) $.
ntp4vc-odd-loop-syntax
  $a wff ( NTP4VCOddLoop A B C ) $.
ntp4vc-outer-branch-syntax
  $a wff ( NTP4VCOuterBranch A B C ) $.
ntp4vc-odd-even-vc-syntax
  $a wff ( NTP4VCOddEvenVC A ) $.

ntp4vc-bool-definition $a |- NTP4VCBool = ( 0 ..^ 2 ) $.
ntp4vc-false-definition $a |- NTP4VCFalse = 0 $.
ntp4vc-true-definition $a |- NTP4VCTrue = 1 $.

ntp4vc-bool-cost-definition $a |- (
  NTP4VCBoolCost A
) = if (
  A = NTP4VCTrue ,
  0 ,
  1
) $.

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
  $d i j A $.

  ntp4vc-inversions-definition $a |- (
    NTP4VCInversions A
  ) = (
    sum_ i e. ( 0 ..^ ( # ` A ) )
      (
        # `
        { j e. ( i ..^ ( # ` A ) ) |
          ( NTP4VCAt A j ) < ( NTP4VCAt A i )
        }
      )
  ) $.
$}

${
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. ZZ
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

ntp4vc-exchange-definition $a |- (
  NTP4VCExchange A B C D
) <->
(
  B
  =
  (
    NTP4VCSet
      ( NTP4VCSet A C ( NTP4VCAt A D ) )
      D
      ( NTP4VCAt A C )
  )
) $.

${
  $d i j A $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i <_ j
            )
            /\
            j < ( # ` A )
          )
          ->
          ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
        )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-odd-sorted-definition $a |- (
    NTP4VCOddSorted A B
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        ( ( 2 x. i ) + 2 ) < B
      )
      ->
      (
        NTP4VCAt A ( ( 2 x. i ) + 1 )
      )
      <_
      (
        NTP4VCAt A ( ( 2 x. i ) + 2 )
      )
    ) $.
$}

${
  $d i A B $.

  ntp4vc-even-sorted-definition $a |- (
    NTP4VCEvenSorted A B
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        ( ( 2 x. i ) + 1 ) < B
      )
      ->
      (
        NTP4VCAt A ( 2 x. i )
      )
      <_
      (
        NTP4VCAt A ( ( 2 x. i ) + 1 )
      )
    ) $.
$}

ntp4vc-inv-rel-definition $a |- (
  NTP4VCInvRel A B C
) <->
(
  (
    C = NTP4VCTrue
    /\
    ( NTP4VCInversions A ) = ( NTP4VCInversions B )
  )
  \/
  (
    C = NTP4VCFalse
    /\
    ( NTP4VCInversions A ) < ( NTP4VCInversions B )
  )
) $.

ntp4vc-odd-invariant-definition $a |- (
  NTP4VCOddInvariant A B C D E
) <->
(
  (
    0 <_ D
    /\
    0 <_ ( ( 2 x. D ) + 1 )
  )
  /\
  (
    ( NTP4VCPerm A C )
    /\
    (
      ( NTP4VCOddSorted C ( ( 2 x. D ) + 1 ) )
      /\
      ( NTP4VCInvRel C B E )
    )
  )
) $.

ntp4vc-odd-after-swap-definition $a |- (
  NTP4VCOddAfterSwap A B C D E
) <->
(
  (
    0 <_ ( ( # ` C ) - ( ( 2 x. E ) + 1 ) )
    /\
    (
      ( # ` D ) - ( ( ( 2 x. E ) + 1 ) + 2 )
    )
    <
    (
      ( # ` C ) - ( ( 2 x. E ) + 1 )
    )
  )
  /\
  (
    (
      0 <_ ( E + 1 )
      /\
      (
        0 <_ ( ( ( 2 x. E ) + 1 ) + 2 )
        /\
        (
          ( ( ( 2 x. E ) + 1 ) + 2 )
          =
          ( ( 2 x. ( E + 1 ) ) + 1 )
        )
      )
    )
    /\
    (
      ( NTP4VCPerm A D )
      /\
      (
        (
          NTP4VCOddSorted D ( ( ( 2 x. E ) + 1 ) + 2 )
        )
        /\
        ( NTP4VCInvRel D B NTP4VCFalse )
      )
    )
  )
) $.

ntp4vc-odd-no-swap-definition $a |- (
  NTP4VCOddNoSwap A B C D E
) <->
(
  (
    0 <_ ( ( # ` C ) - ( ( 2 x. D ) + 1 ) )
    /\
    (
      ( # ` C ) - ( ( ( 2 x. D ) + 1 ) + 2 )
    )
    <
    (
      ( # ` C ) - ( ( 2 x. D ) + 1 )
    )
  )
  /\
  (
    (
      0 <_ ( D + 1 )
      /\
      (
        0 <_ ( ( ( 2 x. D ) + 1 ) + 2 )
        /\
        (
          ( ( ( 2 x. D ) + 1 ) + 2 )
          =
          ( ( 2 x. ( D + 1 ) ) + 1 )
        )
      )
    )
    /\
    (
      ( NTP4VCPerm A C )
      /\
      (
        (
          NTP4VCOddSorted C ( ( ( 2 x. D ) + 1 ) + 2 )
        )
        /\
        ( NTP4VCInvRel C B E )
      )
    )
  )
) $.

${
  $d x A B C D $.

  ntp4vc-odd-swap-definition $a |- (
    NTP4VCOddSwap A B C D
  ) <->
  (
    (
      (
        0 <_ ( ( 2 x. D ) + 1 )
        /\
        ( ( 2 x. D ) + 1 ) < ( # ` C )
      )
      /\
      (
        0 <_ ( ( ( 2 x. D ) + 1 ) + 1 )
        /\
        ( ( ( 2 x. D ) + 1 ) + 1 ) < ( # ` C )
      )
    )
    /\
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` C )
        ->
        (
          (
            NTP4VCExchange
              C
              x
              ( ( 2 x. D ) + 1 )
              ( ( ( 2 x. D ) + 1 ) + 1 )
          )
          ->
          ( NTP4VCOddAfterSwap A B C x D )
        )
      )
  ) $.
$}

ntp4vc-even-initial-definition $a |- (
  NTP4VCEvenInitial A B C D
) <->
(
  (
    (
      0 <_ 0
      /\
      (
        0 <_ 0
        /\
        0 = ( 2 x. 0 )
      )
    )
    /\
    0 <_ 0
  )
  /\
  (
    ( NTP4VCPerm A C )
    /\
    (
      (
        D = NTP4VCTrue
        ->
        ( NTP4VCOddSorted C ( # ` C ) )
      )
      /\
      (
        ( NTP4VCEvenSorted C 0 )
        /\
        (
          ( NTP4VCInvRel C B D )
          /\
          (
            D = NTP4VCTrue
            \/
            ( NTP4VCInversions C ) < ( NTP4VCInversions B )
          )
        )
      )
    )
  )
) $.

ntp4vc-even-invariant-definition $a |- (
  NTP4VCEvenInvariant A B C D E
) <->
(
  (
    0 <_ D
    /\
    0 <_ ( 2 x. D )
  )
  /\
  (
    0 <_ ( 2 x. D )
    /\
    (
      ( NTP4VCPerm A C )
      /\
      (
        (
          E = NTP4VCTrue
          ->
          ( NTP4VCOddSorted C ( # ` C ) )
        )
        /\
        (
          ( NTP4VCEvenSorted C ( 2 x. D ) )
          /\
          (
            ( NTP4VCInvRel C B E )
            /\
            (
              E = NTP4VCTrue
              \/
              ( NTP4VCInversions C ) < ( NTP4VCInversions B )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-even-after-swap-definition $a |- (
  NTP4VCEvenAfterSwap A B C D E
) <->
(
  (
    0 <_ ( ( # ` C ) - ( 2 x. E ) )
    /\
    (
      ( # ` D ) - ( ( 2 x. E ) + 2 )
    )
    <
    (
      ( # ` C ) - ( 2 x. E )
    )
  )
  /\
  (
    (
      0 <_ ( E + 1 )
      /\
      (
        0 <_ ( ( 2 x. E ) + 2 )
        /\
        (
          ( ( 2 x. E ) + 2 )
          =
          ( 2 x. ( E + 1 ) )
        )
      )
    )
    /\
    (
      0 <_ ( ( 2 x. E ) + 2 )
      /\
      (
        ( NTP4VCPerm A D )
        /\
        (
          (
            NTP4VCFalse = NTP4VCTrue
            ->
            ( NTP4VCOddSorted D ( # ` D ) )
          )
          /\
          (
            ( NTP4VCEvenSorted D ( ( 2 x. E ) + 2 ) )
            /\
            (
              ( NTP4VCInvRel D B NTP4VCFalse )
              /\
              (
                NTP4VCFalse = NTP4VCTrue
                \/
                ( NTP4VCInversions D ) < ( NTP4VCInversions B )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-even-no-swap-definition $a |- (
  NTP4VCEvenNoSwap A B C D E
) <->
(
  (
    0 <_ ( ( # ` C ) - ( 2 x. D ) )
    /\
    (
      ( # ` C ) - ( ( 2 x. D ) + 2 )
    )
    <
    (
      ( # ` C ) - ( 2 x. D )
    )
  )
  /\
  (
    (
      0 <_ ( D + 1 )
      /\
      (
        0 <_ ( ( 2 x. D ) + 2 )
        /\
        (
          ( ( 2 x. D ) + 2 )
          =
          ( 2 x. ( D + 1 ) )
        )
      )
    )
    /\
    (
      0 <_ ( ( 2 x. D ) + 2 )
      /\
      (
        ( NTP4VCPerm A C )
        /\
        (
          (
            E = NTP4VCTrue
            ->
            ( NTP4VCOddSorted C ( # ` C ) )
          )
          /\
          (
            ( NTP4VCEvenSorted C ( ( 2 x. D ) + 2 ) )
            /\
            (
              ( NTP4VCInvRel C B E )
              /\
              (
                E = NTP4VCTrue
                \/
                ( NTP4VCInversions C ) < ( NTP4VCInversions B )
              )
            )
          )
        )
      )
    )
  )
) $.

${
  $d x A B C D $.

  ntp4vc-even-swap-definition $a |- (
    NTP4VCEvenSwap A B C D
  ) <->
  (
    (
      (
        0 <_ ( 2 x. D )
        /\
        ( 2 x. D ) < ( # ` C )
      )
      /\
      (
        0 <_ ( ( 2 x. D ) + 1 )
        /\
        ( ( 2 x. D ) + 1 ) < ( # ` C )
      )
    )
    /\
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` C )
        ->
        (
          (
            NTP4VCExchange
              C
              x
              ( 2 x. D )
              ( ( 2 x. D ) + 1 )
          )
          ->
          ( NTP4VCEvenAfterSwap A B C x D )
        )
      )
  ) $.
$}

ntp4vc-even-exit-definition $a |- (
  NTP4VCEvenExit A B C D E
) <->
(
  (
    (
      0 <_ ( NTP4VCBoolCost D )
      /\
      ( NTP4VCBoolCost E ) < ( NTP4VCBoolCost D )
    )
    \/
    (
      ( NTP4VCBoolCost D ) = ( NTP4VCBoolCost E )
      /\
      (
        0 <_ ( NTP4VCInversions B )
        /\
        ( NTP4VCInversions C ) < ( NTP4VCInversions B )
      )
    )
  )
  /\
  (
    ( NTP4VCPerm A C )
    /\
    (
      E = NTP4VCTrue
      ->
      ( NTP4VCSorted C )
    )
  )
) $.

ntp4vc-even-step-definition $a |- (
  NTP4VCEvenStep A B C D E F
) <->
(
  (
    ( 2 x. D ) < ( ( # ` C ) - 1 )
    /\
    (
      (
        0 <_ ( ( 2 x. D ) + 1 )
        /\
        ( ( 2 x. D ) + 1 ) < ( # ` C )
      )
      /\
      (
        (
          0 <_ ( 2 x. D )
          /\
          ( 2 x. D ) < ( # ` C )
        )
        /\
        (
          (
            ( NTP4VCAt C ( ( 2 x. D ) + 1 ) )
            <
            ( NTP4VCAt C ( 2 x. D ) )
            /\
            ( NTP4VCEvenSwap A B C D )
          )
          \/
          (
            -.
            ( NTP4VCAt C ( ( 2 x. D ) + 1 ) )
            <
            ( NTP4VCAt C ( 2 x. D ) )
            /\
            ( NTP4VCEvenNoSwap A B C D F )
          )
        )
      )
    )
  )
  \/
  (
    -. ( 2 x. D ) < ( ( # ` C ) - 1 )
    /\
    ( NTP4VCEvenExit A B C E F )
  )
) $.

${
  $d b i x A B C D E $.

  ntp4vc-even-loop-definition $a |- (
    NTP4VCEvenLoop A B C D E
  ) <->
  (
    ( NTP4VCEvenInitial A B C E )
    /\
    A. i e. ZZ
      A. b e. NTP4VCBool
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` C )
            ->
            (
              ( NTP4VCEvenInvariant A B x i b )
              ->
              ( NTP4VCEvenStep A B x i D b )
            )
          )
  ) $.
$}

ntp4vc-odd-step-definition $a |- (
  NTP4VCOddStep A B C D E F
) <->
(
  (
    ( ( 2 x. D ) + 1 ) < ( ( # ` C ) - 1 )
    /\
    (
      (
        0 <_ ( ( ( 2 x. D ) + 1 ) + 1 )
        /\
        ( ( ( 2 x. D ) + 1 ) + 1 ) < ( # ` C )
      )
      /\
      (
        (
          0 <_ ( ( 2 x. D ) + 1 )
          /\
          ( ( 2 x. D ) + 1 ) < ( # ` C )
        )
        /\
        (
          (
            (
              NTP4VCAt C ( ( ( 2 x. D ) + 1 ) + 1 )
            )
            <
            (
              NTP4VCAt C ( ( 2 x. D ) + 1 )
            )
            /\
            ( NTP4VCOddSwap A B C D )
          )
          \/
          (
            -.
            (
              NTP4VCAt C ( ( ( 2 x. D ) + 1 ) + 1 )
            )
            <
            (
              NTP4VCAt C ( ( 2 x. D ) + 1 )
            )
            /\
            ( NTP4VCOddNoSwap A B C D F )
          )
        )
      )
    )
  )
  \/
  (
    -. ( ( 2 x. D ) + 1 ) < ( ( # ` C ) - 1 )
    /\
    ( NTP4VCEvenLoop A B C E F )
  )
) $.

ntp4vc-odd-initial-definition $a |- (
  NTP4VCOddInitial A B
) <->
(
  (
    0 <_ 0
    /\
    (
      0 <_ 1
      /\
      1 = ( ( 2 x. 0 ) + 1 )
    )
  )
  /\
  (
    ( NTP4VCPerm A B )
    /\
    (
      ( NTP4VCOddSorted B 1 )
      /\
      (
        -.
        NTP4VCTrue = NTP4VCTrue
        ->
        ( NTP4VCInversions B ) < ( NTP4VCInversions B )
      )
    )
  )
) $.

${
  $d b i x A B C $.

  ntp4vc-odd-loop-definition $a |- (
    NTP4VCOddLoop A B C
  ) <->
  (
    ( NTP4VCOddInitial A B )
    /\
    A. i e. ZZ
      A. b e. NTP4VCBool
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` B )
            ->
            (
              ( NTP4VCOddInvariant A B x i b )
              ->
              ( NTP4VCOddStep A B x i C b )
            )
          )
  ) $.
$}

ntp4vc-outer-branch-definition $a |- (
  NTP4VCOuterBranch A B C
) <->
(
  (
    C = NTP4VCFalse
    /\
    ( NTP4VCOddLoop A B C )
  )
  \/
  (
    C = NTP4VCTrue
    /\
    (
      ( NTP4VCSorted B )
      /\
      ( NTP4VCPerm A B )
    )
  )
) $.

${
  $d b x A $.

  ntp4vc-odd-even-vc-definition $a |- (
    NTP4VCOddEvenVC A
  ) <->
  (
    ( NTP4VCPerm A A )
    /\
    A. b e. NTP4VCBool
      A. x e. Word ZZ
        (
          ( # ` x ) = ( # ` A )
          ->
          (
            (
              ( NTP4VCPerm A x )
              /\
              (
                b = NTP4VCTrue
                ->
                ( NTP4VCSorted x )
              )
            )
            ->
            ( NTP4VCOuterBranch A x b )
          )
        )
  ) $.
$}

${
  ntp4vc-array-parameter $e |- A e. Word ZZ $.

  ntp4vc-pearl-verifythis-2017-odd-even-transposition-sort-challenge3-vc
    $a |- ( NTP4VCOddEvenVC A ) $.
$}
