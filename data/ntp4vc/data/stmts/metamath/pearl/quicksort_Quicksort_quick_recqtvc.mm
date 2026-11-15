$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/quicksort_Quicksort_quick_recqtvc: the Bentley-style quicksort
  recursion verification condition states partition-loop initialization and
  preservation, the final pivot swap, and two recursively sorted subarray
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
  NTP4VCPartition directly encodes the source qs_partition definition.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every source
  bound, integer and list quantifier, implication, loop invariant, swap
  continuation, recursive continuation, and conclusion. Let-bound values are
  replaced by direct substitution, and proposition-valued conditionals are
  represented by equivalent exhaustive guarded disjunctions. Every integer
  and integer-list quantifier retains its full source domain. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice
  NTP4VCAt NTP4VCSet
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub
  NTP4VCExchange NTP4VCPartition
  NTP4VCInitial NTP4VCInvariant NTP4VCNextInvariant
  NTP4VCSwapStep NTP4VCStep NTP4VCAllIndices
  NTP4VCAfterRight NTP4VCAfterLeft NTP4VCPivotSwap
  NTP4VCExitResult NTP4VCAllStates NTP4VCEmptyLoop
  NTP4VCRecursive NTP4VCBase NTP4VCQuickRecVC
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
ntp4vc-partition-syntax
  $a wff ( NTP4VCPartition A B C D E F ) $.

ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D E ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H I ) $.
ntp4vc-next-invariant-syntax
  $a wff ( NTP4VCNextInvariant A B C D E F G ) $.
ntp4vc-swap-step-syntax
  $a wff ( NTP4VCSwapStep A B C D E F G ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G ) $.
ntp4vc-all-indices-syntax
  $a wff ( NTP4VCAllIndices A B C D E F G H ) $.
ntp4vc-after-right-syntax
  $a wff ( NTP4VCAfterRight A B C D E ) $.
ntp4vc-after-left-syntax
  $a wff ( NTP4VCAfterLeft A B C D E ) $.
ntp4vc-pivot-swap-syntax
  $a wff ( NTP4VCPivotSwap A B C D E ) $.
ntp4vc-exit-result-syntax
  $a wff ( NTP4VCExitResult A B C D E ) $.
ntp4vc-all-states-syntax
  $a wff ( NTP4VCAllStates A B C D E F ) $.
ntp4vc-empty-loop-syntax
  $a wff ( NTP4VCEmptyLoop A B C ) $.
ntp4vc-recursive-syntax
  $a wff ( NTP4VCRecursive A B C ) $.
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
  $d j A B C D E F $.

  $( A=a1, B=a2, C=l, D=m, E=r, F=v. $)
  ntp4vc-partition-definition $a |- (
    ( NTP4VCPartition A B C D E F )
    <->
    (
      ( NTP4VCPermutSub A B C E )
      /\
      (
        A. j e. ZZ
          (
            (
              C <_ j
              /\
              j < D
            )
            ->
            ( NTP4VCAt B j ) < F
          )
        /\
        (
          A. j e. ZZ
            (
              (
                D < j
                /\
                j < E
              )
              ->
              F <_ ( NTP4VCAt B j )
            )
          /\
          ( NTP4VCAt B D ) = F
        )
      )
    )
  ) $.
$}

${
  $d j A B C D E $.

  $( A=original, B=l, C=r, D=pivot, E=next index. $)
  ntp4vc-initial-definition $a |- (
    ( NTP4VCInitial A B C D E )
    <->
    (
      (
        ( NTP4VCAt A B ) = D
        /\
        (
          B <_ B
          /\
          B < E
        )
      )
      /\
      (
        A. j e. ZZ
          (
            (
              B < j
              /\
              j <_ B
            )
            ->
            ( NTP4VCAt A j ) < D
          )
        /\
        (
          A. j e. ZZ
            (
              (
                B < j
                /\
                j < E
              )
              ->
              D <_ ( NTP4VCAt A j )
            )
          /\
          ( NTP4VCPermutSub A A B C )
        )
      )
    )
  ) $.
$}

${
  $d j A B C D E F G H I $.

  $( A=original, B=current, C=l, D=m, E=i, F=r, G=pivot,
     H=next index, I=last index. $)
  ntp4vc-invariant-definition $a |- (
    ( NTP4VCInvariant A B C D E F G H I )
    <->
    (
      (
        H <_ E
        /\
        E <_ I
      )
      /\
      (
        (
          ( NTP4VCAt B C ) = G
          /\
          (
            C <_ D
            /\
            D < E
          )
        )
        /\
        (
          A. j e. ZZ
            (
              (
                C < j
                /\
                j <_ D
              )
              ->
              ( NTP4VCAt B j ) < G
            )
          /\
          (
            A. j e. ZZ
              (
                (
                  D < j
                  /\
                  j < E
                )
                ->
                G <_ ( NTP4VCAt B j )
              )
            /\
            ( NTP4VCPermutSub A B C F )
          )
        )
      )
    )
  ) $.
$}

${
  $d j A B C D E F G $.

  $( A=original, B=current, C=l, D=m, E=next i, F=r, G=pivot. $)
  ntp4vc-next-invariant-definition $a |- (
    ( NTP4VCNextInvariant A B C D E F G )
    <->
    (
      (
        ( NTP4VCAt B C ) = G
        /\
        (
          C <_ D
          /\
          D < E
        )
      )
      /\
      (
        A. j e. ZZ
          (
            (
              C < j
              /\
              j <_ D
            )
            ->
            ( NTP4VCAt B j ) < G
          )
        /\
        (
          A. j e. ZZ
            (
              (
                D < j
                /\
                j < E
              )
              ->
              G <_ ( NTP4VCAt B j )
            )
          /\
          ( NTP4VCPermutSub A B C F )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G $.

  $( A=original, B=current, C=l, D=m, E=i, F=r, G=pivot. $)
  ntp4vc-swap-step-definition $a |- (
    ( NTP4VCSwapStep A B C D E F G )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          ( NTP4VCExchange B x E ( D + 1 ) )
          ->
          (
            NTP4VCNextInvariant
              A x C ( D + 1 ) ( E + 1 ) F G
          )
        )
      )
  ) $.
$}

ntp4vc-step-definition $a |- (
  ( NTP4VCStep A B C D E F G )
  <->
  (
    (
      0 <_ E
      /\
      E < ( # ` B )
    )
    /\
    (
      (
        ( NTP4VCAt B E ) < G
        /\
        (
          (
            (
              0 <_ E
              /\
              E < ( # ` B )
            )
            /\
            (
              0 <_ ( D + 1 )
              /\
              ( D + 1 ) < ( # ` B )
            )
          )
          /\
          ( NTP4VCSwapStep A B C D E F G )
        )
      )
      \/
      (
        -. ( NTP4VCAt B E ) < G
        /\
        (
          NTP4VCNextInvariant
            A B C D ( E + 1 ) F G
        )
      )
    )
  )
) $.

${
  $d i A B C D E F G H $.

  $( A=original, B=current, C=l, D=m, E=r, F=pivot,
     G=next index, H=last index. $)
  ntp4vc-all-indices-definition $a |- (
    ( NTP4VCAllIndices A B C D E F G H )
    <->
    A. i e. ZZ
      (
        (
          NTP4VCInvariant A B C D i E F G H
        )
        ->
        (
          NTP4VCStep A B C D i E F
        )
      )
  ) $.
$}

${
  $d x A B C D E $.

  $( A=original, B=after-left, C=l, D=right start, E=r. $)
  ntp4vc-after-right-definition $a |- (
    ( NTP4VCAfterRight A B C D E )
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

  $( A=original, B=after-swap, C=l, D=m, E=r. $)
  ntp4vc-after-left-definition $a |- (
    ( NTP4VCAfterLeft A B C D E )
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
            (
              NTP4VCAfterRight A x C ( D + 1 ) E
            )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E $.

  $( A=original, B=current, C=l, D=m, E=r. $)
  ntp4vc-pivot-swap-definition $a |- (
    ( NTP4VCPivotSwap A B C D E )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          ( NTP4VCExchange B x C D )
          ->
          (
            (
              (
                0 <_ ( E - C )
                /\
                ( D - C ) < ( E - C )
              )
              /\
              (
                0 <_ C
                /\
                (
                  C <_ D
                  /\
                  D <_ ( # ` x )
                )
              )
            )
            /\
            ( NTP4VCAfterLeft A x C D E )
          )
        )
      )
  ) $.
$}

ntp4vc-exit-result-definition $a |- (
  ( NTP4VCExitResult A B C D E )
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
        0 <_ D
        /\
        D < ( # ` B )
      )
    )
    /\
    ( NTP4VCPivotSwap A B C D E )
  )
) $.

${
  $d m x A B C D E F $.

  $( A=original, B=l, C=r, D=pivot, E=next index, F=last index. $)
  ntp4vc-all-states-definition $a |- (
    ( NTP4VCAllStates A B C D E F )
    <->
    A. m e. ZZ
      A. x e. Word ZZ
        (
          ( # ` x ) = ( # ` A )
          ->
          (
            (
              NTP4VCAllIndices A x B m C D E F
            )
            /\
            (
              (
                NTP4VCNextInvariant
                  A x B m ( F + 1 ) C D
              )
              ->
              ( NTP4VCExitResult A x B m C )
            )
          )
        )
  ) $.
$}

ntp4vc-empty-loop-definition $a |- (
  ( NTP4VCEmptyLoop A B C )
  <->
  (
    (
      0 <_ B
      /\
      B < ( # ` A )
    )
    /\
    ( NTP4VCPivotSwap A A B B C )
  )
) $.

ntp4vc-recursive-definition $a |- (
  ( NTP4VCRecursive A B C )
  <->
  (
    (
      0 <_ B
      /\
      B < ( # ` A )
    )
    /\
    (
      (
        ( B + 1 ) <_ ( ( C - 1 ) + 1 )
        ->
        (
          (
            NTP4VCInitial
              A B C ( NTP4VCAt A B ) ( B + 1 )
          )
          /\
          (
            NTP4VCAllStates
              A B C ( NTP4VCAt A B ) ( B + 1 ) ( C - 1 )
          )
        )
      )
      /\
      (
        ( ( C - 1 ) + 1 ) < ( B + 1 )
        ->
        ( NTP4VCEmptyLoop A B C )
      )
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
      ( NTP4VCRecursive A B C )
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

  ntp4vc-pearl-quicksort-quick-rec-vc $a |- (
    NTP4VCQuickRecVC C A B
  ) $.
$}
