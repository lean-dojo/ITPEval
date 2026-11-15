$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_naturalrecqtvc: the natural-run
  recursion verification condition preserves sorted-run, subarray
  permutation, unchanged-prefix, merge, and progress invariants through its
  nested continuations. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, D is its distinguished
  inhabitant used by totalized list lookup, and R is the source total preorder
  le. SetMM words over U are exactly arbitrary finite zero-based source lists.

  NTP4VCToNat, NTP4VCAt, and NTP4VCSlice are the source integer-to-natural
  conversion, totalized lookup, and drop-then-take slice. NTP4VCPerm compares
  occurrence counts of every element of U and is equivalent in both
  directions to List.Perm on finite words. NTP4VCPermutSubPrime is the source
  permut_sub': equal lengths and equal prefix and suffix slices, with a
  permutation of the middle slice. NTP4VCPermutSubBound is the distinct
  source permut_sub predicate, including its endpoint bounds and middle-slice
  permutation.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers every typed
  list and integer quantifier, length premise, implication, sortedness
  condition, unchanged-range condition, recursive continuation, and final
  conclusion. The source let-bound n and o2 are substituted by the list
  length and k - 1. Proposition-valued conditionals are represented by
  equivalent exhaustive guarded disjunctions. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSubPrime NTP4VCPermutSubBound
  NTP4VCSortedSub NTP4VCPrefix NTP4VCOutside
  NTP4VCBasicResult NTP4VCNextResult NTP4VCRunPrem NTP4VCInitial
  NTP4VCIAnte NTP4VCProgress NTP4VCHiAnte NTP4VCMergePre
  NTP4VCMergeAnte NTP4VCHiResult NTP4VCA3Loop NTP4VCA2Loop
  NTP4VCILoop NTP4VCMidCompletion NTP4VCMidBody NTP4VCMidLoop
  NTP4VCPositive NTP4VCO1Else NTP4VCO1Body NTP4VCO1Loop
  NTP4VCElse NTP4VCNaturalRecVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.

ntp4vc-perm-syntax $a wff ( NTP4VCPerm A B C ) $.
ntp4vc-permut-sub-prime-syntax
  $a wff ( NTP4VCPermutSubPrime A B C D E ) $.
ntp4vc-permut-sub-bound-syntax
  $a wff ( NTP4VCPermutSubBound A B C D E ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C D E F ) $.
ntp4vc-prefix-syntax
  $a wff ( NTP4VCPrefix A B C D E ) $.
ntp4vc-outside-syntax
  $a wff ( NTP4VCOutside A B C D E F ) $.

ntp4vc-basic-result-syntax
  $a wff ( NTP4VCBasicResult A B C D E F G H ) $.
ntp4vc-next-result-syntax
  $a wff ( NTP4VCNextResult A B C D E F G H I ) $.
ntp4vc-run-prem-syntax
  $a wff ( NTP4VCRunPrem A B C D E F ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D E F G ) $.
ntp4vc-i-ante-syntax
  $a wff ( NTP4VCIAnte A B C D E F G H I J ) $.
ntp4vc-progress-syntax
  $a wff ( NTP4VCProgress A B C D E ) $.
ntp4vc-hi-ante-syntax
  $a wff ( NTP4VCHiAnte A B C D E F G H ) $.
ntp4vc-merge-pre-syntax
  $a wff ( NTP4VCMergePre A B C D E F G H ) $.
ntp4vc-merge-ante-syntax
  $a wff ( NTP4VCMergeAnte A B C D E F G ) $.
ntp4vc-hi-result-syntax
  $a wff ( NTP4VCHiResult A B C D E F G H I J ) $.
ntp4vc-a3-loop-syntax
  $a wff ( NTP4VCA3Loop A B C D E F G H I J ) $.
ntp4vc-a2-loop-syntax
  $a wff ( NTP4VCA2Loop A B C D E F G H I J K ) $.
ntp4vc-i-loop-syntax
  $a wff ( NTP4VCILoop A B C D E F G H I J K ) $.
ntp4vc-mid-completion-syntax
  $a wff ( NTP4VCMidCompletion A B C D E F G H I J ) $.
ntp4vc-mid-body-syntax
  $a wff ( NTP4VCMidBody A B C D E F G H I J K ) $.
ntp4vc-mid-loop-syntax
  $a wff ( NTP4VCMidLoop A B C D E F G H I ) $.
ntp4vc-positive-syntax
  $a wff ( NTP4VCPositive A B C D E F G H I ) $.
ntp4vc-o1-else-syntax
  $a wff ( NTP4VCO1Else A B C D E F G H I ) $.
ntp4vc-o1-body-syntax
  $a wff ( NTP4VCO1Body A B C D E F G H I ) $.
ntp4vc-o1-loop-syntax
  $a wff ( NTP4VCO1Loop A B C D E F G H ) $.
ntp4vc-else-syntax
  $a wff ( NTP4VCElse A B C D E F G H ) $.
ntp4vc-natural-rec-vc-syntax
  $a wff ( NTP4VCNaturalRecVC A B C D E F G ) $.

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

ntp4vc-permut-sub-prime-definition $a |- (
  NTP4VCPermutSubPrime A B C D E
) <->
(
  (
    A e. Word E
    /\
    B e. Word E
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
            E
        )
      )
    )
  )
) $.

ntp4vc-permut-sub-bound-definition $a |- (
  NTP4VCPermutSubBound A B C D E
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
  $d i A B C D E $.

  ntp4vc-prefix-definition $a |- (
    NTP4VCPrefix A B C D E
  ) <->
  (
    (
      A e. Word D
      /\
      B e. Word D
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        ( NTP4VCAt A i E ) = ( NTP4VCAt B i E )
      )
  ) $.
$}

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

ntp4vc-basic-result-definition $a |- (
  NTP4VCBasicResult A B C D E F G H
) <->
(
  (
    (
      E = ( # ` B )
      \/
      (
        ( C + D ) < E
        /\
        E < ( # ` B )
      )
    )
    /\
    ( NTP4VCSortedSub B C E F G H )
  )
  /\
  (
    NTP4VCPermutSubPrime
      A B ( NTP4VCToNat C ) ( # ` B ) F
  )
) $.

ntp4vc-next-result-definition $a |- (
  NTP4VCNextResult A B C D E F G H I
) <->
(
  (
    (
      ( C + ( D + 1 ) ) < E
      /\
      E < F
    )
    /\
    ( NTP4VCSortedSub B C E G H I )
  )
  /\
  (
    (
      NTP4VCPermutSubPrime
        A B ( NTP4VCToNat C ) ( # ` B ) G
    )
    /\
    ( NTP4VCPrefix B A C G I )
  )
) $.

ntp4vc-run-prem-definition $a |- (
  NTP4VCRunPrem A B C D E F
) <->
(
  (
    B < C
    /\
    C <_ ( # ` A )
  )
  /\
  (
    ( NTP4VCSortedSub A B C D E F )
    /\
    (
      C < ( # ` A )
      ->
      -.
      <.
        ( NTP4VCAt A ( C - 1 ) F ) ,
        ( NTP4VCAt A C F )
      >. e. E
    )
  )
) $.

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C D E F G
) <->
(
  (
    (
      ( B + 0 ) < C
      /\
      C < D
    )
    /\
    ( NTP4VCSortedSub A B C E F G )
  )
  /\
  (
    NTP4VCPermutSubPrime
      A A ( NTP4VCToNat B ) ( # ` A ) E
  )
) $.

ntp4vc-i-ante-definition $a |- (
  NTP4VCIAnte A B C D E F G H I J
) <->
(
  (
    (
      0 <_ D
      /\
      D <_ E
    )
    /\
    (
      ( C + D ) < F
      /\
      F < G
    )
  )
  /\
  (
    ( NTP4VCSortedSub B C F H I J )
    /\
    (
      (
        NTP4VCPermutSubPrime
          A B ( NTP4VCToNat C ) ( # ` B ) H
      )
      /\
      ( NTP4VCPrefix B A C H J )
    )
  )
) $.

ntp4vc-progress-definition $a |- (
  NTP4VCProgress A B C D E
) <->
(
  (
    0 <_ A
    /\
    B < A
  )
  /\
  (
    (
      0 <_ C
      /\
      (
        C <_ ( # ` D )
        /\
        ( # ` D ) = ( # ` E )
      )
    )
    /\
    0 <_ B
  )
) $.

ntp4vc-hi-ante-definition $a |- (
  NTP4VCHiAnte A B C D E F G H
) <->
(
  (
    (
      E = ( # ` B )
      \/
      (
        ( C + D ) < E
        /\
        E < ( # ` B )
      )
    )
    /\
    ( NTP4VCSortedSub B C E F G H )
  )
  /\
  (
    (
      NTP4VCPermutSubPrime
        A B ( NTP4VCToNat C ) ( # ` B ) F
    )
    /\
    ( NTP4VCPrefix B A C F H )
  )
) $.

ntp4vc-merge-pre-definition $a |- (
  NTP4VCMergePre A B C D E F G H
) <->
(
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
            E <_ ( # ` B )
            /\
            ( # ` B ) = ( # ` A )
          )
        )
      )
    )
    /\
    ( NTP4VCSortedSub A C D F G H )
  )
  /\
  ( NTP4VCSortedSub A D E F G H )
) $.

ntp4vc-merge-ante-definition $a |- (
  NTP4VCMergeAnte A B C D E F G
) <->
(
  ( NTP4VCSortedSub B C D E F G )
  /\
  (
    (
      NTP4VCPermutSubBound
        A B ( NTP4VCToNat C ) ( NTP4VCToNat D ) E
    )
    /\
    ( NTP4VCOutside B A C D E G )
  )
) $.

ntp4vc-hi-result-definition $a |- (
  NTP4VCHiResult A B C D E F G H I J
) <->
(
  (
    F = G
    /\
    (
      (
        NTP4VCBasicResult
          A B C D G H I J
      )
      /\
      ( NTP4VCPrefix B A C H J )
    )
  )
  \/
  (
    -. F = G
    /\
    (
      NTP4VCNextResult
        A B C E F G H I J
    )
  )
) $.

${
  $d b A B C D E F G H I J $.

  ntp4vc-a3-loop-definition $a |- (
    NTP4VCA3Loop A B C D E F G H I J
  ) <->
  (
    A. b e. Word H
      (
        ( # ` b ) = ( # ` B )
        ->
        (
          ( NTP4VCMergeAnte B b C F H I J )
          ->
          (
            NTP4VCHiResult
              A b C D E F G H I J
          )
        )
      )
  ) $.
$}

${
  $d b h t A B C D E F G H I J K $.

  ntp4vc-a2-loop-definition $a |- (
    NTP4VCA2Loop A B C D E F G H I J K
  ) <->
  (
    A. b e. Word I
      A. t e. Word I
        (
          ( # ` b ) = ( # ` B )
          ->
          (
            ( # ` t ) = ( # ` C )
            ->
            A. h e. ZZ
              (
                ( NTP4VCHiAnte B b G F h I J K )
                ->
                (
                  (
                    NTP4VCMergePre
                      b t D G h I J K
                  )
                  /\
                  (
                    NTP4VCA3Loop
                      A b D E F h H I J K
                  )
                )
              )
          )
        )
  ) $.
$}

${
  $d i A B C D E F G H I J K $.

  ntp4vc-i-loop-definition $a |- (
    NTP4VCILoop A B C D E F G H I J K
  ) <->
  (
    A. i e. ZZ
      (
        (
          NTP4VCIAnte
            A B D i F G H I J K
        )
        ->
        (
          ( NTP4VCProgress E i G B C )
          /\
          (
            NTP4VCA2Loop
              A B C D E i G H I J K
          )
        )
      )
  ) $.
$}

ntp4vc-mid-completion-definition $a |- (
  NTP4VCMidCompletion A B C D E F G H I J
) <->
(
  (
    NTP4VCNextResult
      A B C E F G H I J
  )
  ->
  (
    (
      NTP4VCBasicResult
        A B C D F H I J
    )
    /\
    ( NTP4VCPrefix B A C H J )
  )
) $.

ntp4vc-mid-body-definition $a |- (
  NTP4VCMidBody A B C D E F G H I J K
) <->
(
  (
    NTP4VCILoop
      A B C D E F G H I J K
  )
  /\
  (
    NTP4VCMidCompletion
      A B D E F G H I J K
  )
) $.

${
  $d b m t A B C D E F G H I $.

  ntp4vc-mid-loop-definition $a |- (
    NTP4VCMidLoop A B C D E F G H I
  ) <->
  (
    A. m e. ZZ
      A. b e. Word G
        A. t e. Word G
          (
            ( # ` b ) = ( # ` A )
            ->
            (
              ( # ` t ) = ( # ` B )
              ->
              (
                NTP4VCMidBody
                  A b t C D E m F G H I
              )
            )
          )
  ) $.
$}

ntp4vc-positive-definition $a |- (
  NTP4VCPositive A B C D E F G H I
) <->
(
  ( NTP4VCInitial A C E F G H I )
  /\
  (
    NTP4VCMidLoop
      A B C D ( D - 1 ) F G H I
  )
) $.

ntp4vc-o1-else-definition $a |- (
  NTP4VCO1Else A B C D E F G H I
) <->
(
  (
    0 <_ ( ( D - 1 ) + 1 )
    ->
    (
      NTP4VCPositive
        A B C D E F G H I
    )
  )
  /\
  (
    ( ( D - 1 ) + 1 ) < 0
    ->
    (
      NTP4VCBasicResult
        A A C D E G H I
    )
  )
) $.

ntp4vc-o1-body-definition $a |- (
  NTP4VCO1Body A B C D E F G H I
) <->
(
  (
    E = F
    /\
    (
      NTP4VCBasicResult
        A A C D F G H I
    )
  )
  \/
  (
    -. E = F
    /\
    (
      NTP4VCO1Else
        A B C D E F G H I
    )
  )
) $.

${
  $d o A B C D E F G H $.

  ntp4vc-o1-loop-definition $a |- (
    NTP4VCO1Loop A B C D E F G H
  ) <->
  (
    A. o e. ZZ
      (
        ( NTP4VCRunPrem A C o F G H )
        ->
        (
          NTP4VCO1Body
            A B C D o E F G H
        )
      )
  ) $.
$}

ntp4vc-else-definition $a |- (
  NTP4VCElse A B C D E F G H
) <->
(
  (
    0 <_ C
    /\
    C < ( # ` A )
  )
  /\
  (
    NTP4VCO1Loop
      A B C D E F G H
  )
) $.

ntp4vc-natural-rec-vc-definition $a |- (
  NTP4VCNaturalRecVC A B C D E F G
) <->
(
  (
    ( ( # ` A ) - 1 ) <_ C
    /\
    (
      NTP4VCBasicResult
        A A C D ( # ` A ) E F G
    )
  )
  \/
  (
    -. ( ( # ` A ) - 1 ) <_ C
    /\
    (
      NTP4VCElse
        A B C D ( # ` A ) E F G
    )
  )
) $.

${
  $d x y z A B C D G R U $.

  $( Source arbitrary inhabited carrier elt and its total preorder le. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-default-in-carrier $e |- G e. U $.
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

  $( Source theorem parameters A=a, B=tmp, C=lo, and D=k. $)
  ntp4vc-a-word $e |- A e. Word U $.
  ntp4vc-tmp-word $e |- B e. Word U $.
  ntp4vc-lo-integer $e |- C e. ZZ $.
  ntp4vc-k-integer $e |- D e. ZZ $.

  ntp4vc-fact0 $e |- 0 <_ C $.
  ntp4vc-fact1 $e |- C <_ ( # ` A ) $.
  ntp4vc-fact2 $e |- ( # ` A ) = ( # ` B ) $.
  ntp4vc-fact3 $e |- 0 <_ D $.

  ntp4vc-pearl-natural-mergesort-naturalrec-vc $a |- (
    NTP4VCNaturalRecVC A B C D U R G
  ) $.
$}
