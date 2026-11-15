$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc:
  the bottom-up merge-sort verification condition states the permutation and
  sorted-run invariants for its outer and inner loops, the merge contract, and
  the final sorted-permutation result. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its distinguished
  inhabitant used by totalized list lookup, and R is the source total preorder
  le. SetMM words over U are exactly arbitrary finite zero-based source lists.

  NTP4VCToNat, NTP4VCAt, and NTP4VCSlice are the source integer-to-natural
  conversion, totalized lookup, and drop-then-take slice. NTP4VCPerm compares
  the occurrence count of every element of U; for finite words this is
  equivalent in both directions to List.Perm. NTP4VCPermutSub includes the
  source equal-length and endpoint-bound conjuncts and the permutation of the
  selected slices. NTP4VCSortedSub and NTP4VCSorted use R at every pair of
  source integer indices in the indicated half-open interval.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every typed
  list and integer quantifier, length premise, implication, loop invariant,
  merge premise, conditional branch, and final conclusion. Source let-bound
  values are substituted definitionally, and proposition-valued conditionals
  are represented by equivalent exhaustive guarded disjunctions. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub NTP4VCSorted
  NTP4VCCopy NTP4VCRuns NTP4VCBase NTP4VCOuterInv
  NTP4VCInnerInit NTP4VCInnerInv NTP4VCMergePre NTP4VCOutside
  NTP4VCMergePrem NTP4VCProgress NTP4VCMergeCase NTP4VCFinishCase
  NTP4VCInnerStep NTP4VCInnerLoop NTP4VCOuterTrue NTP4VCOuterStep
  NTP4VCOuterLoop NTP4VCBottomUpVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B C ) $.
ntp4vc-permut-sub-syntax
  $a wff ( NTP4VCPermutSub A B C D E ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C D E F ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-copy-syntax
  $a wff ( NTP4VCCopy A B C D ) $.
ntp4vc-runs-syntax
  $a wff ( NTP4VCRuns A B C D E F G H ) $.
ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B C D E ) $.
ntp4vc-outer-inv-syntax
  $a wff ( NTP4VCOuterInv A B C D E F G ) $.
ntp4vc-inner-init-syntax
  $a wff ( NTP4VCInnerInit A B C D E F ) $.
ntp4vc-inner-inv-syntax
  $a wff ( NTP4VCInnerInv A B C D E F G H ) $.
ntp4vc-merge-pre-syntax
  $a wff ( NTP4VCMergePre A B C D E F G H ) $.
ntp4vc-outside-syntax
  $a wff ( NTP4VCOutside A B C D E F ) $.
ntp4vc-merge-prem-syntax
  $a wff ( NTP4VCMergePrem A B C D E F G ) $.
ntp4vc-progress-syntax
  $a wff ( NTP4VCProgress A B C D E F G H ) $.
ntp4vc-merge-case-syntax
  $a wff ( NTP4VCMergeCase A B C D E F G H I ) $.
ntp4vc-finish-case-syntax
  $a wff ( NTP4VCFinishCase A B C D E F G ) $.
ntp4vc-inner-step-syntax
  $a wff ( NTP4VCInnerStep A B C D E F G H I J ) $.
ntp4vc-inner-loop-syntax
  $a wff ( NTP4VCInnerLoop A B C D E F G H ) $.
ntp4vc-outer-true-syntax
  $a wff ( NTP4VCOuterTrue A B C D E F G H ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C D E F G H ) $.
ntp4vc-outer-loop-syntax
  $a wff ( NTP4VCOuterLoop A B C D E F ) $.
ntp4vc-bottom-up-vc-syntax
  $a wff ( NTP4VCBottomUpVC A B C D ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-nat-sub-definition $a |- (
  NTP4VCNatSub A B
) = if ( B <_ A , ( A - B ) , 0 ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if ( A <_ B , A , B ) $.

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
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d k v A B C $.

  ntp4vc-perm-definition $a |- (
    NTP4VCPerm A B C
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. C
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

ntp4vc-permut-sub-definition $a |- (
  NTP4VCPermutSub A B C D E
) <->
(
  (
    A e. Word E
    /\
    B e. Word E
  )
  /\
  (
    (
      C e. NN0
      /\
      D e. NN0
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        (
          0 <_ C
          /\
          C <_ ( # ` A )
        )
        /\
        (
          (
            0 <_ D
            /\
            D <_ ( # ` A )
          )
          /\
          (
            NTP4VCPerm
              ( NTP4VCSlice A C D )
              ( NTP4VCSlice B C D )
              E
          )
        )
      )
    )
  )
) $.

${
  $d i j A B C D E F $.

  ntp4vc-sorted-sub-definition $a |- (
    NTP4VCSortedSub A B C D E F
  ) <->
  (
    (
      A e. Word D
      /\
      (
        B e. ZZ
        /\
        C e. ZZ
      )
    )
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            B <_ i
            /\
            (
              i < j
              /\
              j < C
            )
          )
          ->
          <.
            ( NTP4VCAt A i F ) ,
            ( NTP4VCAt A j F )
          >. e. E
        )
  ) $.
$}

${
  $d i j A B C D $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A B C D
  ) <->
  (
    A e. Word B
    /\
    A. i e. ZZ
      A. j e. ZZ
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
          <.
            ( NTP4VCAt A i D ) ,
            ( NTP4VCAt A j D )
          >. e. C
        )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-copy-definition $a |- (
    NTP4VCCopy A B C D
  ) <->
  (
    (
      A e. Word C
      /\
      B e. Word C
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          ( NTP4VCAt A i D ) = ( NTP4VCAt B i D )
        )
    )
  ) $.
$}

${
  $d k A B C D E F G H $.

  ntp4vc-runs-definition $a |- (
    NTP4VCRuns A B C D E F G H
  ) <->
  (
    (
      A e. Word F
      /\
      (
        B e. ZZ
        /\
        (
          C e. ZZ
          /\
          D e. ZZ
        )
      )
    )
    /\
    A. k e. ZZ
      (
        (
          C <_ ( k x. B )
          /\
          ( k x. B ) < D
        )
        ->
        (
          NTP4VCSortedSub
            A
            ( k x. B )
            ( NTP4VCMin E ( ( k x. B ) + B ) )
            F G H
        )
      )
  ) $.
$}

ntp4vc-base-definition $a |- (
  NTP4VCBase A B C D E
) <->
(
  1 <_ 1
  /\
  (
    ( NTP4VCPerm A A C )
    /\
    ( NTP4VCRuns A 1 0 B B C D E )
  )
) $.

ntp4vc-outer-inv-definition $a |- (
  NTP4VCOuterInv A B C D E F G
) <->
(
  1 <_ C
  /\
  (
    ( NTP4VCPerm A B E )
    /\
    ( NTP4VCRuns B C 0 D D E F G )
  )
) $.

ntp4vc-inner-init-definition $a |- (
  NTP4VCInnerInit A B C D E F
) <->
(
  (
    0 <_ 0
    /\
    0 = ( ( 2 x. 0 ) x. B )
  )
  /\
  (
    ( NTP4VCPerm A A D )
    /\
    (
      ( NTP4VCRuns A B 0 C C D E F )
      /\
      ( NTP4VCRuns A ( 2 x. B ) 0 0 C D E F )
    )
  )
) $.

ntp4vc-inner-inv-definition $a |- (
  NTP4VCInnerInv A B C D E F G H
) <->
(
  0 <_ ( ( 2 x. C ) x. D )
  /\
  (
    ( NTP4VCPerm A B F )
    /\
    (
      (
        NTP4VCRuns
          B D ( ( 2 x. C ) x. D ) E E F G H
      )
      /\
      (
        NTP4VCRuns
          B ( 2 x. D ) 0 ( ( 2 x. C ) x. D ) E F G H
      )
    )
  )
) $.

ntp4vc-merge-pre-definition $a |- (
  NTP4VCMergePre A B C D E F G H
) <->
(
  (
    0 <_ C
    /\
    (
      C <_ D
      /\
      (
        D <_ E
        /\
        (
          E <_ ( # ` A )
          /\
          ( # ` A ) = ( # ` B )
        )
      )
    )
  )
  /\
  (
    ( NTP4VCSortedSub B C D F G H )
    /\
    ( NTP4VCSortedSub B D E F G H )
  )
) $.

${
  $d i A B C D E F $.

  ntp4vc-outside-definition $a |- (
    NTP4VCOutside A B C D E F
  ) <->
  (
    (
      A e. Word E
      /\
      B e. Word E
    )
    /\
    A. i e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < C
          )
          \/
          (
            D <_ i
            /\
            i < ( # ` A )
          )
        )
        ->
        ( NTP4VCAt A i F ) = ( NTP4VCAt B i F )
      )
  ) $.
$}

ntp4vc-merge-prem-definition $a |- (
  NTP4VCMergePrem A B C D E F G
) <->
(
  ( NTP4VCSortedSub B C D E F G )
  /\
  (
    (
      NTP4VCPermutSub
        A B ( NTP4VCToNat C ) ( NTP4VCToNat D ) E
    )
    /\
    ( NTP4VCOutside B A C D E G )
  )
) $.

ntp4vc-progress-definition $a |- (
  NTP4VCProgress A B C D E F G H
) <->
(
  (
    0 <_
      ( ( E + D ) - ( ( 2 x. C ) x. D ) )
    /\
    (
      ( E + D )
      -
      (
        (
          ( ( 2 x. C ) x. D )
          +
          D
        )
        +
        D
      )
    )
    <
    (
      ( E + D ) - ( ( 2 x. C ) x. D )
    )
  )
  /\
  (
    (
      0 <_
        (
          (
            ( ( 2 x. C ) x. D )
            +
            D
          )
          +
          D
        )
      /\
      (
        (
          ( ( 2 x. C ) x. D )
          +
          D
        )
        +
        D
      )
      =
      (
        ( 2 x. ( C + 1 ) )
        x.
        D
      )
    )
    /\
    (
      ( NTP4VCPerm A B F )
      /\
      (
        (
          NTP4VCRuns
            B D
            (
              (
                ( ( 2 x. C ) x. D )
                +
                D
              )
              +
              D
            )
            E E F G H
        )
        /\
        (
          NTP4VCRuns
            B ( 2 x. D ) 0
            (
              (
                ( ( 2 x. C ) x. D )
                +
                D
              )
              +
              D
            )
            E F G H
        )
      )
    )
  )
) $.

${
  $d b A B C D E F G H I $.

  ntp4vc-merge-case-definition $a |- (
    NTP4VCMergeCase A B C D E F G H I
  ) <->
  (
    (
      NTP4VCMergePre
        A C
        ( ( 2 x. D ) x. E )
        ( ( ( 2 x. D ) x. E ) + E )
        (
          NTP4VCMin
            F
            (
              (
                ( ( 2 x. D ) x. E )
                +
                E
              )
              +
              E
            )
        )
        G H I
    )
    /\
    A. b e. Word G
      (
        ( # ` b ) = ( # ` C )
        ->
        (
          (
            NTP4VCMergePrem
              C b
              ( ( 2 x. D ) x. E )
              (
                NTP4VCMin
                  F
                  (
                    (
                      ( ( 2 x. D ) x. E )
                      +
                      E
                    )
                    +
                    E
                  )
              )
              G H I
          )
          ->
          (
            NTP4VCProgress
              B b D E F G H I
          )
        )
      )
  ) $.
$}

ntp4vc-finish-case-definition $a |- (
  NTP4VCFinishCase A B C D E F G
) <->
(
  (
    0 <_ ( ( 2 x. D ) - C )
    /\
    (
      ( ( 2 x. D ) - ( 2 x. C ) )
      <
      ( ( 2 x. D ) - C )
    )
  )
  /\
  (
    1 <_ ( 2 x. C )
    /\
    (
      ( NTP4VCPerm A B E )
      /\
      ( NTP4VCRuns B ( 2 x. C ) 0 D D E F G )
    )
  )
) $.

ntp4vc-inner-step-definition $a |- (
  NTP4VCInnerStep A B C D E F G H I J
) <->
(
  (
    (
      ( ( 2 x. E ) x. F )
      <
      ( G - F )
    )
    /\
    (
      NTP4VCMergeCase
        A C D E F G H I J
    )
  )
  \/
  (
    -.
    (
      ( ( 2 x. E ) x. F )
      <
      ( G - F )
    )
    /\
    (
      NTP4VCFinishCase
        B D F G H I J
    )
  )
) $.

${
  $d b i t A B C D E F G H $.

  ntp4vc-inner-loop-definition $a |- (
    NTP4VCInnerLoop A B C D E F G H
  ) <->
  (
    A. i e. ZZ
      A. t e. Word F
        A. b e. Word F
          (
            ( # ` t ) = ( # ` A )
            ->
            (
              ( # ` b ) = ( # ` C )
              ->
              (
                (
                  NTP4VCInnerInv
                    C b i D E F G H
                )
                ->
                (
                  NTP4VCInnerStep
                    t B C b i D E F G H
                )
              )
            )
          )
  ) $.
$}

ntp4vc-outer-true-definition $a |- (
  NTP4VCOuterTrue A B C D E F G H
) <->
(
  ( NTP4VCInnerInit C D E F G H )
  /\
  ( NTP4VCInnerLoop B A C D E F G H )
) $.

ntp4vc-outer-step-definition $a |- (
  NTP4VCOuterStep A B C D E F G H
) <->
(
  (
    D < E
    /\
    ( NTP4VCOuterTrue A B C D E F G H )
  )
  \/
  (
    -. D < E
    /\
    (
      ( NTP4VCSorted C F G H )
      /\
      ( NTP4VCPerm A C F )
    )
  )
) $.

${
  $d b l t A B C D E F $.

  ntp4vc-outer-loop-definition $a |- (
    NTP4VCOuterLoop A B C D E F
  ) <->
  (
    A. l e. ZZ
      A. t e. Word D
        A. b e. Word D
          (
            ( # ` t ) = ( # ` B )
            ->
            (
              ( # ` b ) = ( # ` A )
              ->
              (
                ( NTP4VCOuterInv A b l C D E F )
                ->
                (
                  NTP4VCOuterStep
                    A t b l C D E F
                )
              )
            )
          )
  ) $.
$}

${
  $d t A B C D $.

  ntp4vc-bottom-up-vc-definition $a |- (
    NTP4VCBottomUpVC A B C D
  ) <->
  (
    A. t e. Word B
      (
        ( NTP4VCCopy t A B D )
        ->
        (
          ( NTP4VCBase A ( # ` A ) B C D )
          /\
          (
            NTP4VCOuterLoop
              A t ( # ` A ) B C D
          )
        )
      )
  ) $.
$}

${
  $d x y z A D R U $.

  $( Source arbitrary inhabited carrier elt and its total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-default-in-carrier $e |- D e. U $.
  ntp4vc-le-relation $e |- R C_ ( U X. U ) $.
  ntp4vc-le-reflexive $e |- A. x e. U
    <. x , x >. e. R $.
  ntp4vc-le-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.
  ntp4vc-le-total $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      <. y , x >. e. R
    ) $.

  $( Source theorem parameter A=a. $)
  ntp4vc-a-word $e |- A e. Word U $.

  ntp4vc-pearl-bottom-up-mergesort-vc $a |- (
    NTP4VCBottomUpVC A U R D
  ) $.
$}
