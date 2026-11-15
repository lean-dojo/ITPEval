$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_natural_mergesortqtvc: the natural
  merge-sort verification condition states the initial sorted-run and
  permutation invariants, discovery of adjacent natural runs, the merge
  contract, loop progress, and the final sorted-permutation result. This file
  contains no proof.
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
  natural-run boundary premise, merge premise, conditional branch, and final
  conclusion. The source let-bound n is substituted by the list length, and
  proposition-valued conditionals are represented by equivalent exhaustive
  guarded disjunctions. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub NTP4VCSorted
  NTP4VCCopy NTP4VCBase NTP4VCFirstAnte NTP4VCFirstInit
  NTP4VCSecondAnte NTP4VCProgress NTP4VCOutside NTP4VCNext
  NTP4VCHiPrem NTP4VCHiBody NTP4VCMidPrem NTP4VCMidElse
  NTP4VCMidBody NTP4VCLoTrue NTP4VCSecondStep NTP4VCSecondLoop
  NTP4VCFirstBody NTP4VCFirstLoop NTP4VCElse NTP4VCNaturalVC
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
ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B C D E ) $.
ntp4vc-first-ante-syntax
  $a wff ( NTP4VCFirstAnte A B C D E F G ) $.
ntp4vc-first-init-syntax
  $a wff ( NTP4VCFirstInit A B C D E F ) $.
ntp4vc-second-ante-syntax
  $a wff ( NTP4VCSecondAnte A B C D E F G H I ) $.
ntp4vc-progress-syntax
  $a wff ( NTP4VCProgress A B C D E F G H ) $.
ntp4vc-outside-syntax
  $a wff ( NTP4VCOutside A B C D E F ) $.
ntp4vc-next-syntax
  $a wff ( NTP4VCNext A B C D E F G H I J ) $.
ntp4vc-hi-prem-syntax
  $a wff ( NTP4VCHiPrem A B C D E F ) $.
ntp4vc-hi-body-syntax
  $a wff ( NTP4VCHiBody A B C D E F G H I J K L M ) $.
ntp4vc-mid-prem-syntax
  $a wff ( NTP4VCMidPrem A B C D E F ) $.
ntp4vc-mid-else-syntax
  $a wff ( NTP4VCMidElse A B C D E F G H I J K L ) $.
ntp4vc-mid-body-syntax
  $a wff ( NTP4VCMidBody A B C D E F G H I J K L ) $.
ntp4vc-lo-true-syntax
  $a wff ( NTP4VCLoTrue A B C D E F G H I J K ) $.
ntp4vc-second-step-syntax
  $a wff ( NTP4VCSecondStep A B C D E F G H I J K ) $.
ntp4vc-second-loop-syntax
  $a wff ( NTP4VCSecondLoop A B C D E F G H ) $.
ntp4vc-first-body-syntax
  $a wff ( NTP4VCFirstBody A B C D E F G H I ) $.
ntp4vc-first-loop-syntax
  $a wff ( NTP4VCFirstLoop A B C D E F ) $.
ntp4vc-else-syntax
  $a wff ( NTP4VCElse A B C D E ) $.
ntp4vc-natural-vc-syntax
  $a wff ( NTP4VCNaturalVC A B C D ) $.

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

ntp4vc-base-definition $a |- (
  NTP4VCBase A B C D E
) <->
(
  (
    (
      0 <_ 0
      /\
      0 <_ B
    )
    /\
    ( NTP4VCSortedSub A 0 0 C D E )
  )
  /\
  ( NTP4VCPerm A A C )
) $.

ntp4vc-first-ante-definition $a |- (
  NTP4VCFirstAnte A B C D E F G
) <->
(
  (
    (
      0 <_ C
      /\
      C <_ D
    )
    /\
    ( NTP4VCSortedSub B 0 C E F G )
  )
  /\
  ( NTP4VCPerm A B E )
) $.

ntp4vc-first-init-definition $a |- (
  NTP4VCFirstInit A B C D E F
) <->
(
  (
    0 <_ 0
    /\
    0 <_ C
  )
  /\
  (
    (
      B <_ B
      /\
      B <_ C
    )
    /\
    (
      ( NTP4VCSortedSub A 0 B D E F )
      /\
      ( NTP4VCPerm A A D )
    )
  )
) $.

ntp4vc-second-ante-definition $a |- (
  NTP4VCSecondAnte A B C D E F G H I
) <->
(
  (
    0 <_ C
    /\
    C <_ F
  )
  /\
  (
    (
      D <_ E
      /\
      E <_ F
    )
    /\
    (
      ( NTP4VCSortedSub B 0 E G H I )
      /\
      (
        (
          C = 0
          \/
          (
            E <_ C
            /\
            D < E
          )
        )
        /\
        ( NTP4VCPerm A B G )
      )
    )
  )
) $.

ntp4vc-progress-definition $a |- (
  NTP4VCProgress A B C D E F G H
) <->
(
  (
    0 <_ ( E - C )
    /\
    ( E - D ) < ( E - C )
  )
  /\
  (
    (
      0 <_ D
      /\
      D <_ E
    )
    /\
    (
      ( NTP4VCSortedSub B 0 D F G H )
      /\
      ( NTP4VCPerm A B F )
    )
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

ntp4vc-next-definition $a |- (
  NTP4VCNext A B C D E F G H I J
) <->
(
  (
    D = 0
    /\
    (
      (
        0 <_ ( C - D )
        /\
        ( C - E ) < ( C - D )
      )
      /\
      (
        (
          0 <_ E
          /\
          E <_ C
        )
        /\
        (
          (
            F <_ E
            /\
            E <_ C
          )
          /\
          (
            ( NTP4VCSortedSub B 0 E H I J )
            /\
            (
              (
                E = 0
                \/
                (
                  E <_ E
                  /\
                  F < E
                )
              )
              /\
              ( NTP4VCPerm A B H )
            )
          )
        )
      )
    )
  )
  \/
  (
    -. D = 0
    /\
    (
      (
        0 <_ ( C - D )
        /\
        ( C - E ) < ( C - D )
      )
      /\
      (
        (
          0 <_ E
          /\
          E <_ C
        )
        /\
        (
          (
            F <_ G
            /\
            G <_ C
          )
          /\
          (
            ( NTP4VCSortedSub B 0 G H I J )
            /\
            (
              (
                E = 0
                \/
                (
                  G <_ E
                  /\
                  F < G
                )
              )
              /\
              ( NTP4VCPerm A B H )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-hi-prem-definition $a |- (
  NTP4VCHiPrem A B C D E F
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

${
  $d b A B C D E F G H I J K L M $.

  ntp4vc-hi-body-definition $a |- (
    NTP4VCHiBody A B C D E F G H I J K L M
  ) <->
  (
    (
      (
        0 <_ F
        /\
        F <_ G
      )
      /\
      (
        G <_ H
        /\
        (
          H <_ ( # ` D )
          /\
          ( # ` D ) = ( # ` C )
        )
      )
    )
    /\
    (
      ( NTP4VCSortedSub C F G K L M )
      /\
      (
        ( NTP4VCSortedSub C G H K L M )
        /\
        A. b e. Word K
          (
            ( # ` b ) = ( # ` C )
            ->
            (
              (
                ( NTP4VCSortedSub b F H K L M )
                /\
                (
                  NTP4VCPermutSub
                    C b
                    ( NTP4VCToNat F )
                    ( NTP4VCToNat H )
                    K
                )
              )
              /\
              ( NTP4VCOutside b C F H K M )
              ->
              (
                NTP4VCNext
                  B b E F H I J K L M
              )
            )
          )
      )
    )
  ) $.
$}

ntp4vc-mid-prem-definition $a |- (
  NTP4VCMidPrem A B C D E F
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

${
  $d h A B C D E F G H I J K L $.

  ntp4vc-mid-else-definition $a |- (
    NTP4VCMidElse A B C D E F G H I J K L
  ) <->
  (
    (
      0 <_ G
      /\
      G < ( # ` C )
    )
    /\
    A. h e. ZZ
      (
        ( NTP4VCHiPrem C G h J K L )
        ->
        (
          NTP4VCHiBody
            A B C D E F G h H I J K L
        )
      )
  ) $.
$}

ntp4vc-mid-body-definition $a |- (
  NTP4VCMidBody A B C D E F G H I J K L
) <->
(
  (
    G = E
    /\
    (
      (
        F = 0
        /\
        (
          ( NTP4VCSorted C J K L )
          /\
          ( NTP4VCPerm A C J )
        )
      )
      \/
      (
        -. F = 0
        /\
        (
          NTP4VCProgress
            A C H I E J K L
        )
      )
    )
  )
  \/
  (
    -. G = E
    /\
    (
      NTP4VCMidElse
        A B C D E F G H I J K L
    )
  )
) $.

${
  $d m A B C D E F G H I J K $.

  ntp4vc-lo-true-definition $a |- (
    NTP4VCLoTrue A B C D E F G H I J K
  ) <->
  (
    (
      0 <_ F
      /\
      F < ( # ` C )
    )
    /\
    A. m e. ZZ
      (
        ( NTP4VCMidPrem C F m I J K )
        ->
        (
          NTP4VCMidBody
            A B C D E F m G H I J K
        )
      )
  ) $.
$}

ntp4vc-second-step-definition $a |- (
  NTP4VCSecondStep A B C D E F G H I J K
) <->
(
  (
    F < ( E - 1 )
    /\
    (
      NTP4VCLoTrue
        A B C D E F G H I J K
    )
  )
  \/
  (
    -. F < ( E - 1 )
    /\
    (
      NTP4VCProgress
        A C G H E I J K
    )
  )
) $.

${
  $d b f l t A B C D E F G H $.

  ntp4vc-second-loop-definition $a |- (
    NTP4VCSecondLoop A B C D E F G H
  ) <->
  (
    A. l e. ZZ
      A. f e. ZZ
        A. t e. Word F
          A. b e. Word F
            (
              ( # ` t ) = ( # ` C )
              ->
              (
                ( # ` b ) = ( # ` B )
                ->
                (
                  (
                    NTP4VCSecondAnte
                      B b l E f D F G H
                  )
                  ->
                  (
                    NTP4VCSecondStep
                      A B b t D l E f F G H
                  )
                )
              )
            )
  ) $.
$}

ntp4vc-first-body-definition $a |- (
  NTP4VCFirstBody A B C D E F G H I
) <->
(
  ( NTP4VCFirstInit F D C G H I )
  /\
  (
    NTP4VCSecondLoop
      A F E C D G H I
  )
) $.

${
  $d b f t A B C D E F $.

  ntp4vc-first-loop-definition $a |- (
    NTP4VCFirstLoop A B C D E F
  ) <->
  (
    A. f e. ZZ
      A. t e. Word D
        A. b e. Word D
          (
            ( # ` t ) = ( # ` B )
            ->
            (
              ( # ` b ) = ( # ` A )
              ->
              (
                (
                  NTP4VCFirstAnte
                    A b f C D E F
                )
                ->
                (
                  NTP4VCFirstBody
                    A B C f t b D E F
                )
              )
            )
          )
  ) $.
$}

${
  $d t A B C D E $.

  ntp4vc-else-definition $a |- (
    NTP4VCElse A B C D E
  ) <->
  (
    A. t e. Word C
      (
        ( NTP4VCCopy t A C E )
        ->
        (
          ( NTP4VCBase A B C D E )
          /\
          (
            NTP4VCFirstLoop
              A t B C D E
          )
        )
      )
  ) $.
$}

ntp4vc-natural-vc-definition $a |- (
  NTP4VCNaturalVC A B C D
) <->
(
  (
    ( # ` A ) <_ 1
    /\
    (
      ( NTP4VCSorted A B C D )
      /\
      ( NTP4VCPerm A A B )
    )
  )
  \/
  (
    -. ( # ` A ) <_ 1
    /\
    (
      NTP4VCElse
        A ( # ` A ) B C D
    )
  )
) $.

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

  ntp4vc-pearl-natural-mergesort-vc $a |- (
    NTP4VCNaturalVC A U R D
  ) $.
$}
