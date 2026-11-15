$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/quicksort_Traditional_quick_recqtvc: the traditional two-pointer
  quicksort recursion verification condition states the bidirectional scan
  invariants, swaps, variant decreases, and recursively sorted subarray
  permutation obligations. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat,
  NTP4VCAt, NTP4VCSet, and NTP4VCSlice reproduce the source Int.toNat,
  totalized list lookup with default zero, List.set, and drop-then-take slice.

  NTP4VCPerm compares the occurrence count of every integer and is
  bidirectionally equivalent to List.Perm on finite integer words.
  NTP4VCPermutSub is exactly the exported permut_sub' representation of the
  Why3 array permut_sub predicate, and NTP4VCSortedSub is the source
  integer-indexed sorted_sub1 predicate. NTP4VCExchange defines its second
  list as the exact post-state obtained by swapping the two indicated
  positions in its first list, matching the primary Why3 ArraySwap semantics
  rather than the reversed equation in the exported Lean helper.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every source
  bound, integer and list quantifier, implication, loop invariant, scan
  continuation, swap continuation, recursive continuation, and conclusion.
  Let-bound values are replaced by direct substitution, and
  proposition-valued conditionals are represented by equivalent exhaustive
  guarded disjunctions. Every integer and integer-list quantifier retains its
  full source domain. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCAt NTP4VCSet
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub NTP4VCExchange
  NTP4VCAllLeClosed NTP4VCAllLeHalfOpen
  NTP4VCAllGeHalfOpen NTP4VCAllGeOpen
  NTP4VCLoopInvariant
  NTP4VCAfterRightRecursion NTP4VCAfterLeftRecursion
  NTP4VCFinishSwapContinuation NTP4VCFinishResult
  NTP4VCLoopSwapContinuation NTP4VCLoopSwapResult
  NTP4VCJProgress NTP4VCJ1Result NTP4VCAllJ1 NTP4VCJScan
  NTP4VCIProgress NTP4VCI1Result NTP4VCAllI1
  NTP4VCLoopStateResult NTP4VCAllLoopStates
  NTP4VCRecursiveBranch NTP4VCBase NTP4VCQuickRecVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-exchange-syntax
  $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-all-le-closed-syntax
  $a wff ( NTP4VCAllLeClosed A B C D ) $.
ntp4vc-all-le-half-open-syntax
  $a wff ( NTP4VCAllLeHalfOpen A B C D ) $.
ntp4vc-all-ge-half-open-syntax
  $a wff ( NTP4VCAllGeHalfOpen A B C D ) $.
ntp4vc-all-ge-open-syntax
  $a wff ( NTP4VCAllGeOpen A B C D ) $.

ntp4vc-loop-invariant-syntax
  $a wff ( NTP4VCLoopInvariant A B C D E F G ) $.
ntp4vc-after-right-recursion-syntax
  $a wff ( NTP4VCAfterRightRecursion A B C D E ) $.
ntp4vc-after-left-recursion-syntax
  $a wff ( NTP4VCAfterLeftRecursion A B C D E ) $.
ntp4vc-finish-swap-continuation-syntax
  $a wff ( NTP4VCFinishSwapContinuation A B C D E ) $.
ntp4vc-finish-result-syntax
  $a wff ( NTP4VCFinishResult A B C D E ) $.
ntp4vc-loop-swap-continuation-syntax
  $a wff ( NTP4VCLoopSwapContinuation A B C D E F G H I ) $.
ntp4vc-loop-swap-result-syntax
  $a wff ( NTP4VCLoopSwapResult A B C D E F G H I ) $.
ntp4vc-j-progress-syntax
  $a wff ( NTP4VCJProgress A B C D E F ) $.
ntp4vc-j1-result-syntax
  $a wff ( NTP4VCJ1Result A B C D E F G H I ) $.
ntp4vc-all-j1-syntax
  $a wff ( NTP4VCAllJ1 A B C D E F G H ) $.
ntp4vc-j-scan-syntax
  $a wff ( NTP4VCJScan A B C D E F G H ) $.
ntp4vc-i-progress-syntax
  $a wff ( NTP4VCIProgress A B C D E F ) $.
ntp4vc-i1-result-syntax
  $a wff ( NTP4VCI1Result A B C D E F G H ) $.
ntp4vc-all-i1-syntax
  $a wff ( NTP4VCAllI1 A B C D E F G ) $.
ntp4vc-loop-state-result-syntax
  $a wff ( NTP4VCLoopStateResult A B C D E F G ) $.
ntp4vc-all-loop-states-syntax
  $a wff ( NTP4VCAllLoopStates A B C D ) $.
ntp4vc-recursive-branch-syntax
  $a wff ( NTP4VCRecursiveBranch A B C ) $.
ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B C ) $.
ntp4vc-quick-rec-vc-syntax
  $a wff ( NTP4VCQuickRecVC A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if (
  B <_ A ,
  ( A - B ) ,
  0
) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if (
  A <_ B ,
  A ,
  B
) $.

ntp4vc-slice-start-definition $a |- (
  NTP4VCSliceStart A B
) = (
  NTP4VCMin ( NTP4VCToNat B ) ( # ` A )
) $.

ntp4vc-slice-len-definition $a |- (
  NTP4VCSliceLen A B C
) = (
  NTP4VCMin
    ( NTP4VCNatSub ( NTP4VCToNat C ) ( NTP4VCToNat B ) )
    ( ( # ` A ) - ( NTP4VCSliceStart A B ) )
) $.

${
  $d k A B C $.

  ntp4vc-slice-definition $a |- (
    NTP4VCSlice A B C
  ) = (
    k e. ( 0 ..^ ( NTP4VCSliceLen A B C ) ) |->
      ( A ` ( ( NTP4VCSliceStart A B ) + k ) )
  ) $.
$}

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
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    ( NTP4VCPerm A B )
    <->
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
    )
  ) $.
$}

ntp4vc-permut-sub-definition $a |- (
  ( NTP4VCPermutSub A B C D )
  <->
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
      (
        ( NTP4VCSlice A 0 C ) = ( NTP4VCSlice B 0 C )
        /\
        (
          ( NTP4VCSlice A D ( # ` A ) )
          =
          ( NTP4VCSlice B D ( # ` B ) )
          /\
          (
            NTP4VCPerm
              ( NTP4VCSlice A C D )
              ( NTP4VCSlice B C D )
          )
        )
      )
    )
  )
) $.

${
  $d i j A B C $.

  ntp4vc-sorted-sub-definition $a |- (
    ( NTP4VCSortedSub A B C )
    <->
    (
      A e. Word ZZ
      /\
      A. i e. ZZ
        A. j e. ZZ
          (
            (
              B <_ i
              /\
              (
                i <_ j
                /\
                j < C
              )
            )
            ->
            ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
          )
    )
  ) $.
$}

ntp4vc-exchange-definition $a |- (
  ( NTP4VCExchange A B C D )
  <->
  B = (
    NTP4VCSet
      ( NTP4VCSet A C ( NTP4VCAt A D ) )
      D
      ( NTP4VCAt A C )
  )
) $.

${
  $d k A B C D $.

  ntp4vc-all-le-closed-definition $a |- (
    ( NTP4VCAllLeClosed A B C D )
    <->
    A. k e. ZZ
      (
        (
          B <_ k
          /\
          k <_ C
        )
        ->
        ( NTP4VCAt A k ) <_ D
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-all-le-half-open-definition $a |- (
    ( NTP4VCAllLeHalfOpen A B C D )
    <->
    A. k e. ZZ
      (
        (
          B <_ k
          /\
          k < C
        )
        ->
        ( NTP4VCAt A k ) <_ D
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-all-ge-half-open-definition $a |- (
    ( NTP4VCAllGeHalfOpen A B C D )
    <->
    A. k e. ZZ
      (
        (
          B <_ k
          /\
          k < C
        )
        ->
        D <_ ( NTP4VCAt A k )
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-all-ge-open-definition $a |- (
    ( NTP4VCAllGeOpen A B C D )
    <->
    A. k e. ZZ
      (
        (
          B < k
          /\
          k < C
        )
        ->
        D <_ ( NTP4VCAt A k )
      )
  ) $.
$}

$(
  A=original, B=current, C=l, D=r, E=j, F=i, G=pivot.
$)
ntp4vc-loop-invariant-definition $a |- (
  ( NTP4VCLoopInvariant A B C D E F G )
  <->
  (
    (
      C <_ F
      /\
      F < ( D - 1 )
    )
    /\
    (
      ( NTP4VCAllLeClosed B C F G )
      /\
      (
        (
          C < E
          /\
          E <_ D
        )
        /\
        (
          ( NTP4VCAllGeHalfOpen B E D G )
          /\
          (
            ( NTP4VCPermutSub A B C D )
            /\
            ( NTP4VCAt B C ) = G
          )
        )
      )
    )
  )
) $.

${
  $d x A B C D E $.

  $( A=original, B=after-left, C=l, D=right start, E=r. $)
  ntp4vc-after-right-recursion-definition $a |- (
    ( NTP4VCAfterRightRecursion A B C D E )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          (
            ( NTP4VCSortedSub x D E )
            /\
            ( NTP4VCPermutSub B x D E )
          )
          ->
          (
            ( NTP4VCSortedSub x C E )
            /\
            ( NTP4VCPermutSub A x C E )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E $.

  $( A=original, B=after-swap, C=l, D=middle, E=r. $)
  ntp4vc-after-left-recursion-definition $a |- (
    ( NTP4VCAfterLeftRecursion A B C D E )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          (
            ( NTP4VCSortedSub x C D )
            /\
            ( NTP4VCPermutSub B x C D )
          )
          ->
          (
            (
              (
                0 <_ ( E - C )
                /\
                ( E - ( D + 1 ) ) < ( E - C )
              )
              /\
              (
                0 <_ ( D + 1 )
                /\
                (
                  ( D + 1 ) <_ E
                  /\
                  E <_ ( # ` x )
                )
              )
            )
            /\
            ( NTP4VCAfterRightRecursion A x C ( D + 1 ) E )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E $.

  $( A=original, B=current, C=l, D=r, E=j1. $)
  ntp4vc-finish-swap-continuation-definition $a |- (
    ( NTP4VCFinishSwapContinuation A B C D E )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          ( NTP4VCExchange B x C E )
          ->
          (
            (
              (
                0 <_ ( D - C )
                /\
                ( E - C ) < ( D - C )
              )
              /\
              (
                0 <_ C
                /\
                (
                  C <_ E
                  /\
                  E <_ ( # ` x )
                )
              )
            )
            /\
            ( NTP4VCAfterLeftRecursion A x C E D )
          )
        )
      )
  ) $.
$}

ntp4vc-finish-result-definition $a |- (
  ( NTP4VCFinishResult A B C D E )
  <->
  (
    (
      (
        0 <_ C
        /\
        C < ( # ` B )
      )
      /\
      (
        0 <_ E
        /\
        E < ( # ` B )
      )
    )
    /\
    ( NTP4VCFinishSwapContinuation A B C D E )
  )
) $.

${
  $d x A B C D E F G H I $.

  $( A=original, B=current, C=l, D=r, E=j, F=i,
     G=i1, H=j1, I=pivot. $)
  ntp4vc-loop-swap-continuation-definition $a |- (
    ( NTP4VCLoopSwapContinuation A B C D E F G H I )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          ( NTP4VCExchange B x G H )
          ->
          (
            (
              0 <_ ( E - F )
              /\
              ( H - G ) < ( E - F )
            )
            /\
            (
              (
                C <_ G
                /\
                G < ( D - 1 )
              )
              /\
              (
                ( NTP4VCAllLeClosed x C G I )
                /\
                (
                  (
                    C < H
                    /\
                    H <_ D
                  )
                  /\
                  (
                    ( NTP4VCAllGeHalfOpen x H D I )
                    /\
                    (
                      ( NTP4VCPermutSub A x C D )
                      /\
                      ( NTP4VCAt x C ) = I
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

ntp4vc-loop-swap-result-definition $a |- (
  ( NTP4VCLoopSwapResult A B C D E F G H I )
  <->
  (
    (
      (
        0 <_ G
        /\
        G < ( # ` B )
      )
      /\
      (
        0 <_ H
        /\
        H < ( # ` B )
      )
    )
    /\
    ( NTP4VCLoopSwapContinuation A B C D E F G H I )
  )
) $.

$( A=current, B=l, C=r, D=j, E=j1, F=pivot. $)
ntp4vc-j-progress-definition $a |- (
  ( NTP4VCJProgress A B C D E F )
  <->
  (
    (
      0 <_ E
      /\
      ( E - 1 ) < E
    )
    /\
    (
      (
        B <_ ( E - 1 )
        /\
        ( E - 1 ) < D
      )
      /\
      ( NTP4VCAllGeOpen A ( E - 1 ) C F )
    )
  )
) $.

$( A=original, B=current, C=l, D=r, E=j, F=i,
   G=i1, H=j1, I=pivot. $)
ntp4vc-j1-result-definition $a |- (
  ( NTP4VCJ1Result A B C D E F G H I )
  <->
  (
    (
      0 <_ H
      /\
      H < ( # ` B )
    )
    /\
    (
      (
        I < ( NTP4VCAt B H )
        /\
        (
          (
            H = C
            /\
            (
              (
                H <_ G
                /\
                ( NTP4VCFinishResult A B C D H )
              )
              \/
              (
                -. H <_ G
                /\
                ( NTP4VCLoopSwapResult A B C D E F G H I )
              )
            )
          )
          \/
          (
            -. H = C
            /\
            ( NTP4VCJProgress B C D E H I )
          )
        )
      )
      \/
      (
        -. I < ( NTP4VCAt B H )
        /\
        (
          (
            H <_ G
            /\
            ( NTP4VCFinishResult A B C D H )
          )
          \/
          (
            -. H <_ G
            /\
            ( NTP4VCLoopSwapResult A B C D E F G H I )
          )
        )
      )
    )
  )
) $.

${
  $d j A B C D E F G H $.

  $( A=original, B=current, C=l, D=r, E=j, F=i,
     G=i1, H=pivot. $)
  ntp4vc-all-j1-definition $a |- (
    ( NTP4VCAllJ1 A B C D E F G H )
    <->
    A. j e. ZZ
      (
        (
          (
            C <_ j
            /\
            j < E
          )
          /\
          ( NTP4VCAllGeOpen B j D H )
        )
        ->
        ( NTP4VCJ1Result A B C D E F G j H )
      )
  ) $.
$}

$( A=original, B=current, C=l, D=r, E=j, F=i,
   G=i1, H=pivot. $)
ntp4vc-j-scan-definition $a |- (
  ( NTP4VCJScan A B C D E F G H )
  <->
  (
    (
      (
        C <_ ( E - 1 )
        /\
        ( E - 1 ) < E
      )
      /\
      ( NTP4VCAllGeOpen B ( E - 1 ) D H )
    )
    /\
    ( NTP4VCAllJ1 A B C D E F G H )
  )
) $.

$( A=current, B=l, C=r, D=i, E=i1, F=pivot. $)
ntp4vc-i-progress-definition $a |- (
  ( NTP4VCIProgress A B C D E F )
  <->
  (
    (
      0 <_ ( C - E )
      /\
      ( C - ( E + 1 ) ) < ( C - E )
    )
    /\
    (
      (
        D < ( E + 1 )
        /\
        ( E + 1 ) < C
      )
      /\
      ( NTP4VCAllLeHalfOpen A B ( E + 1 ) F )
    )
  )
) $.

$( A=original, B=current, C=l, D=r, E=j, F=i,
   G=i1, H=pivot. $)
ntp4vc-i1-result-definition $a |- (
  ( NTP4VCI1Result A B C D E F G H )
  <->
  (
    (
      0 <_ G
      /\
      G < ( # ` B )
    )
    /\
    (
      (
        ( NTP4VCAt B G ) < H
        /\
        (
          (
            G = ( D - 1 )
            /\
            ( NTP4VCJScan A B C D E F G H )
          )
          \/
          (
            -. G = ( D - 1 )
            /\
            ( NTP4VCIProgress B C D F G H )
          )
        )
      )
      \/
      (
        -. ( NTP4VCAt B G ) < H
        /\
        ( NTP4VCJScan A B C D E F G H )
      )
    )
  )
) $.

${
  $d i A B C D E F G $.

  $( A=original, B=current, C=l, D=r, E=j, F=i, G=pivot. $)
  ntp4vc-all-i1-definition $a |- (
    ( NTP4VCAllI1 A B C D E F G )
    <->
    A. i e. ZZ
      (
        (
          (
            F < i
            /\
            i < D
          )
          /\
          ( NTP4VCAllLeHalfOpen B C i G )
        )
        ->
        ( NTP4VCI1Result A B C D E F i G )
      )
  ) $.
$}

$( A=original, B=current, C=l, D=r, E=j, F=i, G=pivot. $)
ntp4vc-loop-state-result-definition $a |- (
  ( NTP4VCLoopStateResult A B C D E F G )
  <->
  (
    (
      (
        F < ( F + 1 )
        /\
        ( F + 1 ) < D
      )
      /\
      ( NTP4VCAllLeHalfOpen B C ( F + 1 ) G )
    )
    /\
    ( NTP4VCAllI1 A B C D E F G )
  )
) $.

${
  $d i j x A B C D $.

  $( A=original, B=l, C=r, D=pivot. $)
  ntp4vc-all-loop-states-definition $a |- (
    ( NTP4VCAllLoopStates A B C D )
    <->
    A. j e. ZZ
      A. i e. ZZ
        A. x e. Word ZZ
          (
            ( # ` x ) = ( # ` A )
            ->
            (
              ( NTP4VCLoopInvariant A x B C j i D )
              ->
              ( NTP4VCLoopStateResult A x B C j i D )
            )
          )
  ) $.
$}

ntp4vc-recursive-branch-definition $a |- (
  ( NTP4VCRecursiveBranch A B C )
  <->
  (
    (
      0 <_ B
      /\
      B < ( # ` A )
    )
    /\
    (
      ( NTP4VCLoopInvariant A A B C C B ( NTP4VCAt A B ) )
      /\
      ( NTP4VCAllLoopStates A B C ( NTP4VCAt A B ) )
    )
  )
) $.

ntp4vc-base-definition $a |- (
  ( NTP4VCBase A B C )
  <->
  (
    ( NTP4VCSortedSub A B C )
    /\
    ( NTP4VCPermutSub A A B C )
  )
) $.

ntp4vc-quick-rec-vc-definition $a |- (
  ( NTP4VCQuickRecVC A B C )
  <->
  (
    (
      ( B + 1 ) < C
      /\
      ( NTP4VCRecursiveBranch A B C )
    )
    \/
    (
      -. ( B + 1 ) < C
      /\
      ( NTP4VCBase A B C )
    )
  )
) $.

${
  $( Source theorem parameters A=l, B=r, and C=a. $)

  ntp4vc-l-integer $e |- A e. ZZ $.
  ntp4vc-r-integer $e |- B e. ZZ $.
  ntp4vc-a-list $e |- C e. Word ZZ $.

  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- A <_ B $.
  ntp4vc-fact2 $e |- B <_ ( # ` C ) $.

  ntp4vc-pearl-quicksort-traditional-quick-rec-vc $a |- (
    NTP4VCQuickRecVC C A B
  ) $.
$}
