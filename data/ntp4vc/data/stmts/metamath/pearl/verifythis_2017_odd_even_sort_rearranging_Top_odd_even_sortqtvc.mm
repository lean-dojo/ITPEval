$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_odd_even_sortqtvc:
  the odd-even sorting verification condition preserves permutation and
  alternating local-order invariants while swaps strictly decrease a
  weighted entropy measure, culminating in a sorted permutation. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer arrays are represented exactly by arbitrary finite SetMM words over
  ZZ. NTP4VCToNat and NTP4VCAt reproduce the exported Int.toNat conversion
  and totalized integer-list lookup with default zero. NTP4VCPerm compares
  every integer's multiplicity and is therefore equivalent in both directions
  to finite-list permutation. NTP4VCExchange is the primary Why3 exchange
  relation: its second array is exactly its first array with the selected
  entries swapped.

  NTP4VCArrayMax is the source ghost array_max operator. Its generated
  upper-bound condition remains the antecedent of the final verification
  condition. NTP4VCEntropy is the source half-open integer sum of
  i * (m - a[i]). Parity, sortedness, odd-index local order, and even-index
  local order are expanded over the full integer domain.

  The remaining predicates only factor the original nested loop verification
  condition. Expanding their biconditional definitions recovers every source
  integer, Boolean, and intermediate-array quantifier; every length premise,
  permutation invariant, parity invariant, local-order invariant, swap
  continuation, entropy decrease, loop variant, conditional branch, and final
  sorted-permutation conclusion. Booleans use the exact two-element carrier,
  and proposition-valued conditionals use equivalent exhaustive guarded
  disjunctions.

  Every declaration below is syntax, a faithful definition, or Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCBool NTP4VCFalse NTP4VCTrue
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCArrayMax NTP4VCEntropy
  NTP4VCPerm NTP4VCExchange NTP4VCEven NTP4VCOdd NTP4VCSorted
  NTP4VCOddPrefix NTP4VCOddFull NTP4VCEvenPrefix
  NTP4VCOddInvariant NTP4VCEvenInvariant
  NTP4VCOddAfterSwap NTP4VCOddNoSwap NTP4VCOddSwap
  NTP4VCEvenAfterSwap NTP4VCEvenNoSwap NTP4VCEvenSwap
  NTP4VCEvenExit NTP4VCEvenStep NTP4VCOddExit NTP4VCOddStep
  NTP4VCOddInitial NTP4VCOuterThen NTP4VCOuterBranch
$.

ntp4vc-bool-syntax $a class NTP4VCBool $.
ntp4vc-false-syntax $a class NTP4VCFalse $.
ntp4vc-true-syntax $a class NTP4VCTrue $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-array-max-syntax $a class ( NTP4VCArrayMax A ) $.
ntp4vc-entropy-syntax $a class ( NTP4VCEntropy A B ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-exchange-syntax $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-even-syntax $a wff ( NTP4VCEven A ) $.
ntp4vc-odd-syntax $a wff ( NTP4VCOdd A ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A ) $.
ntp4vc-odd-prefix-syntax $a wff ( NTP4VCOddPrefix A B ) $.
ntp4vc-odd-full-syntax $a wff ( NTP4VCOddFull A ) $.
ntp4vc-even-prefix-syntax $a wff ( NTP4VCEvenPrefix A B ) $.

ntp4vc-odd-invariant-syntax
  $a wff ( NTP4VCOddInvariant A B C D E F ) $.
ntp4vc-even-invariant-syntax
  $a wff ( NTP4VCEvenInvariant A B C D E F ) $.
ntp4vc-odd-after-swap-syntax
  $a wff ( NTP4VCOddAfterSwap A B C D E F ) $.
ntp4vc-odd-no-swap-syntax
  $a wff ( NTP4VCOddNoSwap A B C D E F ) $.
ntp4vc-odd-swap-syntax
  $a wff ( NTP4VCOddSwap A B C D E ) $.
ntp4vc-even-after-swap-syntax
  $a wff ( NTP4VCEvenAfterSwap A B C D E F ) $.
ntp4vc-even-no-swap-syntax
  $a wff ( NTP4VCEvenNoSwap A B C D E F ) $.
ntp4vc-even-swap-syntax
  $a wff ( NTP4VCEvenSwap A B C D E ) $.
ntp4vc-even-exit-syntax
  $a wff ( NTP4VCEvenExit A B C D E F ) $.
ntp4vc-even-step-syntax
  $a wff ( NTP4VCEvenStep A B C D E F G ) $.
ntp4vc-odd-exit-syntax
  $a wff ( NTP4VCOddExit A B C D E F ) $.
ntp4vc-odd-step-syntax
  $a wff ( NTP4VCOddStep A B C D E F G ) $.
ntp4vc-odd-initial-syntax
  $a wff ( NTP4VCOddInitial A B C ) $.
ntp4vc-outer-then-syntax
  $a wff ( NTP4VCOuterThen A B C D ) $.
ntp4vc-outer-branch-syntax
  $a wff ( NTP4VCOuterBranch A B C D ) $.

ntp4vc-bool-definition $a |- NTP4VCBool = ( 0 ..^ 2 ) $.
ntp4vc-false-definition $a |- NTP4VCFalse = 0 $.
ntp4vc-true-definition $a |- NTP4VCTrue = 1 $.

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
  $d k A B $.

  ntp4vc-entropy-definition $a |- (
    NTP4VCEntropy A B
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      (
        k
        x.
        (
          B
          -
          ( NTP4VCAt A k )
        )
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
  $d k A $.

  ntp4vc-even-definition $a |- (
    NTP4VCEven A
  ) <->
  E. k e. ZZ A = ( 2 x. k ) $.
$}

${
  $d k A $.

  ntp4vc-odd-definition $a |- (
    NTP4VCOdd A
  ) <->
  E. k e. ZZ A = ( ( 2 x. k ) + 1 ) $.
$}

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
  $d j A B $.

  ntp4vc-odd-prefix-definition $a |- (
    NTP4VCOddPrefix A B
  ) <->
  A. j e. ZZ
    (
      (
        (
          0 <_ j
          /\
          j < B
        )
        /\
        ( NTP4VCOdd j )
      )
      ->
      ( NTP4VCAt A j ) <_ ( NTP4VCAt A ( j + 1 ) )
    ) $.
$}

${
  $d j A $.

  ntp4vc-odd-full-definition $a |- (
    NTP4VCOddFull A
  ) <->
  A. j e. ZZ
    (
      (
        (
          0 <_ j
          /\
          j < ( ( # ` A ) - 1 )
        )
        /\
        ( NTP4VCOdd j )
      )
      ->
      ( NTP4VCAt A j ) <_ ( NTP4VCAt A ( j + 1 ) )
    ) $.
$}

${
  $d j A B $.

  ntp4vc-even-prefix-definition $a |- (
    NTP4VCEvenPrefix A B
  ) <->
  A. j e. ZZ
    (
      (
        (
          0 <_ j
          /\
          j < B
        )
        /\
        ( NTP4VCEven j )
      )
      ->
      ( NTP4VCAt A j ) <_ ( NTP4VCAt A ( j + 1 ) )
    ) $.
$}

ntp4vc-odd-invariant-definition $a |- (
  NTP4VCOddInvariant A B C D E F
) <->
(
  ( NTP4VCPerm A C )
  /\
  (
    (
      0 <_ E
      /\
      E <_ ( # ` C )
    )
    /\
    (
      ( NTP4VCOdd E )
      /\
      (
        (
          F = NTP4VCTrue
          ->
          ( NTP4VCEntropy C D ) = ( NTP4VCEntropy B D )
        )
        /\
        (
          (
            F = NTP4VCTrue
            ->
            ( NTP4VCOddPrefix C E )
          )
          /\
          (
            F = NTP4VCFalse
            ->
            ( NTP4VCEntropy C D ) < ( NTP4VCEntropy B D )
          )
        )
      )
    )
  )
) $.

ntp4vc-even-invariant-definition $a |- (
  NTP4VCEvenInvariant A B C D E F
) <->
(
  ( NTP4VCPerm A C )
  /\
  (
    (
      0 <_ E
      /\
      E <_ ( # ` C )
    )
    /\
    (
      ( NTP4VCEven E )
      /\
      (
        (
          F = NTP4VCTrue
          ->
          ( NTP4VCEntropy C D ) = ( NTP4VCEntropy B D )
        )
        /\
        (
          (
            F = NTP4VCTrue
            ->
            ( NTP4VCOddFull C )
          )
          /\
          (
            (
              F = NTP4VCTrue
              ->
              ( NTP4VCEvenPrefix C E )
            )
            /\
            (
              F = NTP4VCFalse
              ->
              ( NTP4VCEntropy C D ) < ( NTP4VCEntropy B D )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-odd-after-swap-definition $a |- (
  NTP4VCOddAfterSwap A B C D E F
) <->
(
  (
    (
      0 <_ ( ( # ` C ) - F )
      /\
      (
        ( # ` D ) - ( F + 2 )
      )
      <
      (
        ( # ` C ) - F
      )
    )
    /\
    ( NTP4VCPerm A D )
  )
  /\
  (
    (
      0 <_ ( F + 2 )
      /\
      ( F + 2 ) <_ ( # ` D )
    )
    /\
    (
      ( NTP4VCOdd ( F + 2 ) )
      /\
      (
        (
          NTP4VCFalse = NTP4VCTrue
          ->
          ( NTP4VCEntropy D E ) = ( NTP4VCEntropy B E )
        )
        /\
        (
          (
            NTP4VCFalse = NTP4VCTrue
            ->
            ( NTP4VCOddPrefix D ( F + 2 ) )
          )
          /\
          (
            -. NTP4VCFalse = NTP4VCTrue
            ->
            ( NTP4VCEntropy D E ) < ( NTP4VCEntropy B E )
          )
        )
      )
    )
  )
) $.

ntp4vc-odd-no-swap-definition $a |- (
  NTP4VCOddNoSwap A B C D E F
) <->
(
  (
    (
      0 <_ ( ( # ` C ) - E )
      /\
      (
        ( # ` C ) - ( E + 2 )
      )
      <
      (
        ( # ` C ) - E
      )
    )
    /\
    ( NTP4VCPerm A C )
  )
  /\
  (
    (
      0 <_ ( E + 2 )
      /\
      ( E + 2 ) <_ ( # ` C )
    )
    /\
    (
      ( NTP4VCOdd ( E + 2 ) )
      /\
      (
        (
          F = NTP4VCTrue
          ->
          ( NTP4VCEntropy C D ) = ( NTP4VCEntropy B D )
        )
        /\
        (
          (
            F = NTP4VCTrue
            ->
            ( NTP4VCOddPrefix C ( E + 2 ) )
          )
          /\
          (
            F = NTP4VCFalse
            ->
            ( NTP4VCEntropy C D ) < ( NTP4VCEntropy B D )
          )
        )
      )
    )
  )
) $.

${
  $d x A B C D E $.

  ntp4vc-odd-swap-definition $a |- (
    NTP4VCOddSwap A B C D E
  ) <->
  (
    (
      (
        ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
        /\
        0 <_ E
      )
      /\
      (
        E < ( E + 1 )
        /\
        ( E + 1 ) < ( # ` C )
      )
    )
    /\
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` C )
        ->
        (
          (
            ( NTP4VCExchange C x E ( E + 1 ) )
            /\
            ( NTP4VCEntropy x D ) < ( NTP4VCEntropy C D )
          )
          ->
          ( NTP4VCOddAfterSwap A B C x D E )
        )
      )
  ) $.
$}

ntp4vc-even-after-swap-definition $a |- (
  NTP4VCEvenAfterSwap A B C D E F
) <->
(
  (
    (
      0 <_ ( ( # ` C ) - F )
      /\
      (
        ( # ` D ) - ( F + 2 )
      )
      <
      (
        ( # ` C ) - F
      )
    )
    /\
    ( NTP4VCPerm A D )
  )
  /\
  (
    (
      0 <_ ( F + 2 )
      /\
      ( F + 2 ) <_ ( # ` D )
    )
    /\
    (
      ( NTP4VCEven ( F + 2 ) )
      /\
      (
        (
          NTP4VCFalse = NTP4VCTrue
          ->
          ( NTP4VCEntropy D E ) = ( NTP4VCEntropy B E )
        )
        /\
        (
          (
            NTP4VCFalse = NTP4VCTrue
            ->
            ( NTP4VCOddFull D )
          )
          /\
          (
            (
              NTP4VCFalse = NTP4VCTrue
              ->
              ( NTP4VCEvenPrefix D ( F + 2 ) )
            )
            /\
            (
              -. NTP4VCFalse = NTP4VCTrue
              ->
              ( NTP4VCEntropy D E ) < ( NTP4VCEntropy B E )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-even-no-swap-definition $a |- (
  NTP4VCEvenNoSwap A B C D E F
) <->
(
  (
    (
      0 <_ ( ( # ` C ) - E )
      /\
      (
        ( # ` C ) - ( E + 2 )
      )
      <
      (
        ( # ` C ) - E
      )
    )
    /\
    ( NTP4VCPerm A C )
  )
  /\
  (
    (
      0 <_ ( E + 2 )
      /\
      ( E + 2 ) <_ ( # ` C )
    )
    /\
    (
      ( NTP4VCEven ( E + 2 ) )
      /\
      (
        (
          F = NTP4VCTrue
          ->
          ( NTP4VCEntropy C D ) = ( NTP4VCEntropy B D )
        )
        /\
        (
          (
            F = NTP4VCTrue
            ->
            ( NTP4VCOddFull C )
          )
          /\
          (
            (
              F = NTP4VCTrue
              ->
              ( NTP4VCEvenPrefix C ( E + 2 ) )
            )
            /\
            (
              F = NTP4VCFalse
              ->
              ( NTP4VCEntropy C D ) < ( NTP4VCEntropy B D )
            )
          )
        )
      )
    )
  )
) $.

${
  $d x A B C D E $.

  ntp4vc-even-swap-definition $a |- (
    NTP4VCEvenSwap A B C D E
  ) <->
  (
    (
      (
        ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
        /\
        0 <_ E
      )
      /\
      (
        E < ( E + 1 )
        /\
        ( E + 1 ) < ( # ` C )
      )
    )
    /\
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` C )
        ->
        (
          (
            ( NTP4VCExchange C x E ( E + 1 ) )
            /\
            ( NTP4VCEntropy x D ) < ( NTP4VCEntropy C D )
          )
          ->
          ( NTP4VCEvenAfterSwap A B C x D E )
        )
      )
  ) $.
$}

ntp4vc-even-exit-definition $a |- (
  NTP4VCEvenExit A B C D E F
) <->
(
  (
    0
    <_
    (
      ( NTP4VCEntropy B D )
      +
      if ( E = NTP4VCTrue , 0 , 1 )
    )
    /\
    (
      (
        ( NTP4VCEntropy C D )
        +
        if ( F = NTP4VCTrue , 0 , 1 )
      )
      <
      (
        ( NTP4VCEntropy B D )
        +
        if ( E = NTP4VCTrue , 0 , 1 )
      )
    )
  )
  /\
  (
    ( NTP4VCPerm A C )
    /\
    (
      F = NTP4VCTrue
      ->
      ( NTP4VCSorted C )
    )
  )
) $.

ntp4vc-even-step-definition $a |- (
  NTP4VCEvenStep A B C D E F G
) <->
(
  (
    E < ( ( # ` C ) - 1 )
    /\
    (
      (
        0 <_ ( E + 1 )
        /\
        ( E + 1 ) < ( # ` C )
      )
      /\
      (
        (
          0 <_ E
          /\
          E < ( # ` C )
        )
        /\
        (
          (
            ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
            /\
            ( NTP4VCEvenSwap A B C D E )
          )
          \/
          (
            -. ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
            /\
            ( NTP4VCEvenNoSwap A B C D E F )
          )
        )
      )
    )
  )
  \/
  (
    -. E < ( ( # ` C ) - 1 )
    /\
    ( NTP4VCEvenExit A B C D G F )
  )
) $.

${
  $d b i x A B C D E F $.

  ntp4vc-odd-exit-definition $a |- (
    NTP4VCOddExit A B C D E F
  ) <->
  (
    ( NTP4VCEvenInvariant A B C D 0 E )
    /\
    A. i e. ZZ
      A. b e. NTP4VCBool
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` C )
            ->
            (
              ( NTP4VCEvenInvariant A B x D i b )
              ->
              ( NTP4VCEvenStep A B x D i b F )
            )
          )
  ) $.
$}

ntp4vc-odd-step-definition $a |- (
  NTP4VCOddStep A B C D E F G
) <->
(
  (
    E < ( ( # ` C ) - 1 )
    /\
    (
      (
        0 <_ ( E + 1 )
        /\
        ( E + 1 ) < ( # ` C )
      )
      /\
      (
        (
          0 <_ E
          /\
          E < ( # ` C )
        )
        /\
        (
          (
            ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
            /\
            ( NTP4VCOddSwap A B C D E )
          )
          \/
          (
            -. ( NTP4VCAt C ( E + 1 ) ) < ( NTP4VCAt C E )
            /\
            ( NTP4VCOddNoSwap A B C D E F )
          )
        )
      )
    )
  )
  \/
  (
    -. E < ( ( # ` C ) - 1 )
    /\
    ( NTP4VCOddExit A B C D F G )
  )
) $.

ntp4vc-odd-initial-definition $a |- (
  NTP4VCOddInitial A B C
) <->
(
  ( NTP4VCPerm A B )
  /\
  (
    (
      0 <_ 1
      /\
      1 <_ ( # ` B )
    )
    /\
    (
      ( NTP4VCOdd 1 )
      /\
      (
        ( NTP4VCOddPrefix B 1 )
        /\
        (
          -. NTP4VCTrue = NTP4VCTrue
          ->
          ( NTP4VCEntropy B C ) < ( NTP4VCEntropy B C )
        )
      )
    )
  )
) $.

${
  $d b i x A B C D $.

  ntp4vc-outer-then-definition $a |- (
    NTP4VCOuterThen A B C D
  ) <->
  (
    ( NTP4VCOddInitial A B C )
    /\
    A. i e. ZZ
      A. b e. NTP4VCBool
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` B )
            ->
            (
              ( NTP4VCOddInvariant A B x C i b )
              ->
              ( NTP4VCOddStep A B x C i b D )
            )
          )
  ) $.
$}

ntp4vc-outer-branch-definition $a |- (
  NTP4VCOuterBranch A B C D
) <->
(
  (
    D = NTP4VCFalse
    /\
    ( NTP4VCOuterThen A B C D )
  )
  \/
  (
    D = NTP4VCTrue
    /\
    (
      ( NTP4VCSorted B )
      /\
      ( NTP4VCPerm A B )
    )
  )
) $.

${
  $d A j o x $.

  ntp4vc-array-parameter
    $e |- A e. Word ZZ $.
  ntp4vc-array-max-type
    $e |- ( NTP4VCArrayMax A ) e. ZZ $.
  ntp4vc-fact0
    $e |- 0 < ( # ` A ) $.

  ntp4vc-pearl-verifythis-2017-odd-even-sort-vc $a |- (
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < ( # ` A )
        )
        ->
        ( NTP4VCAt A j ) <_ ( NTP4VCArrayMax A )
      )
    ->
    (
      ( NTP4VCPerm A A )
      /\
      A. o e. NTP4VCBool
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` A )
            ->
            (
              (
                ( NTP4VCPerm A x )
                /\
                (
                  o = NTP4VCTrue
                  ->
                  ( NTP4VCSorted x )
                )
              )
              ->
              (
                NTP4VCOuterBranch
                  A x ( NTP4VCArrayMax A ) o
              )
            )
          )
    )
  ) $.
$}
