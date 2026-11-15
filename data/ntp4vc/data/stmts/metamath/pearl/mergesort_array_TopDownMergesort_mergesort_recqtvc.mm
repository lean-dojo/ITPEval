$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_array_TopDownMergesort_mergesort_recqtvc: the top-down
  mergesort recursive verification condition preserves sorted subarrays and
  subarray permutations through its two recursive calls and final merge
  continuation. This file contains no proof.
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
  permutation. NTP4VCSortedSub and NTP4VCOutside directly encode the source
  integer-indexed sortedness and unchanged-outside predicates.

  NTP4VCTDiv2 is signed integer division by 2 truncated toward zero, and
  NTP4VCMid substitutes the source let-bound midpoint. The remaining
  predicates only factor the original nested verification condition.
  Expanding their biconditional definitions recovers every typed list and
  integer quantifier, length premise, implication, recursive continuation,
  merge continuation, and final conclusion. The proposition-valued
  conditional is represented by equivalent exhaustive guarded disjunctions.

  The official Lean and Isabelle sources use the truncating quotient
  operations Int.tdiv and cdiv for the midpoint. The official Rocq source
  spells that position with Z.rem, which is substantively different; this
  declaration records the agreeing Lean/Isabelle quotient statement, as in
  the repository's established NTP4VC Metamath convention. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCTDiv2 NTP4VCMid
  NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSubPrime NTP4VCPermutSubBound
  NTP4VCSortedSub NTP4VCOutside
  NTP4VCBase NTP4VCMerged NTP4VCMergeObligations
  NTP4VCAllSecond NTP4VCSecond NTP4VCAllFirst
  NTP4VCRecursive NTP4VCMergesortRecVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-mid-syntax $a class ( NTP4VCMid A B ) $.
ntp4vc-nat-sub-syntax $a class ( NTP4VCNatSub A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-slice-start-syntax $a class ( NTP4VCSliceStart A B ) $.
ntp4vc-slice-len-syntax $a class ( NTP4VCSliceLen A B C ) $.
ntp4vc-slice-syntax $a class ( NTP4VCSlice A B C ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B C ) $.
ntp4vc-permut-sub-prime-syntax
  $a wff ( NTP4VCPermutSubPrime A B C D E ) $.
ntp4vc-permut-sub-bound-syntax
  $a wff ( NTP4VCPermutSubBound A B C D E ) $.
ntp4vc-sorted-sub-syntax
  $a wff ( NTP4VCSortedSub A B C D E F ) $.
ntp4vc-outside-syntax
  $a wff ( NTP4VCOutside A B C D E F ) $.

ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B C D E F ) $.
ntp4vc-merged-syntax
  $a wff ( NTP4VCMerged A B C D E F G ) $.
ntp4vc-merge-obligations-syntax
  $a wff ( NTP4VCMergeObligations A B C D E F G H I ) $.
ntp4vc-all-second-syntax
  $a wff ( NTP4VCAllSecond A B C D E F G H I ) $.
ntp4vc-second-syntax
  $a wff ( NTP4VCSecond A B C D E F G H I ) $.
ntp4vc-all-first-syntax
  $a wff ( NTP4VCAllFirst A B C D E F G H ) $.
ntp4vc-recursive-syntax
  $a wff ( NTP4VCRecursive A B C D E F G ) $.
ntp4vc-mergesort-rec-vc-syntax
  $a wff ( NTP4VCMergesortRecVC A B C D E F G ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-mid-definition $a |- (
  NTP4VCMid A B
) = (
  A + ( NTP4VCTDiv2 ( B - A ) )
) $.

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

ntp4vc-base-definition $a |- (
  NTP4VCBase A B C D E F
) <->
(
  ( NTP4VCSortedSub A B C D E F )
  /\
  (
    NTP4VCPermutSubPrime
      A A
      ( NTP4VCToNat B )
      ( NTP4VCToNat C )
      D
  )
) $.

${
  $d b A B C D E F G $.

  ntp4vc-merged-definition $a |- (
    NTP4VCMerged A B C D E F G
  ) <->
  (
    A. b e. Word E
      (
        ( # ` b ) = ( # ` B )
        ->
        (
          (
            (
              ( NTP4VCSortedSub b C D E F G )
              /\
              (
                NTP4VCPermutSubBound
                  B b
                  ( NTP4VCToNat C )
                  ( NTP4VCToNat D )
                  E
              )
            )
            /\
            ( NTP4VCOutside b B C D E G )
          )
          ->
          (
            ( NTP4VCSortedSub b C D E F G )
            /\
            (
              NTP4VCPermutSubPrime
                A b
                ( NTP4VCToNat C )
                ( NTP4VCToNat D )
                E
            )
          )
        )
      )
  ) $.
$}

ntp4vc-merge-obligations-definition $a |- (
  NTP4VCMergeObligations A B C D E F G H I
) <->
(
  (
    (
      (
        0 <_ D
        /\
        (
          D <_ E
          /\
          (
            E <_ F
            /\
            (
              F <_ ( # ` C )
              /\
              ( # ` C ) = ( # ` B )
            )
          )
        )
      )
      /\
      ( NTP4VCSortedSub B D E G H I )
    )
    /\
    ( NTP4VCSortedSub B E F G H I )
  )
  /\
  ( NTP4VCMerged A B D F G H I )
) $.

${
  $d b t A B C D E F G H I $.

  ntp4vc-all-second-definition $a |- (
    NTP4VCAllSecond A B C D E F G H I
  ) <->
  (
    A. t e. Word G
      A. b e. Word G
        (
          ( # ` t ) = ( # ` C )
          ->
          (
            ( # ` b ) = ( # ` B )
            ->
            (
              (
                ( NTP4VCSortedSub b E F G H I )
                /\
                (
                  NTP4VCPermutSubPrime
                    B b
                    ( NTP4VCToNat E )
                    ( NTP4VCToNat F )
                    G
                )
              )
              ->
              (
                NTP4VCMergeObligations
                  A b t D E F G H I
              )
            )
          )
        )
  ) $.
$}

ntp4vc-second-definition $a |- (
  NTP4VCSecond A B C D E F G H I
) <->
(
  (
    (
      0 <_ ( F - D )
      /\
      ( F - E ) < ( F - D )
    )
    /\
    (
      0 <_ E
      /\
      (
        E <_ F
        /\
        (
          F <_ ( # ` B )
          /\
          ( # ` B ) = ( # ` C )
        )
      )
    )
  )
  /\
  (
    NTP4VCAllSecond
      A B C D E F G H I
  )
) $.

${
  $d b t A B C D E F G H $.

  ntp4vc-all-first-definition $a |- (
    NTP4VCAllFirst A B C D E F G H
  ) <->
  (
    A. t e. Word F
      A. b e. Word F
        (
          ( # ` t ) = ( # ` B )
          ->
          (
            ( # ` b ) = ( # ` A )
            ->
            (
              (
                ( NTP4VCSortedSub b C D F G H )
                /\
                (
                  NTP4VCPermutSubPrime
                    A b
                    ( NTP4VCToNat C )
                    ( NTP4VCToNat D )
                    F
                )
              )
              ->
              (
                NTP4VCSecond
                  A b t C D E F G H
              )
            )
          )
        )
  ) $.
$}

ntp4vc-recursive-definition $a |- (
  NTP4VCRecursive A B C D E F G
) <->
(
  -. 2 = 0
  /\
  (
    (
      (
        0 <_ ( B - A )
        /\
        (
          ( ( NTP4VCMid A B ) - A )
          <
          ( B - A )
        )
      )
      /\
      (
        0 <_ A
        /\
        (
          A <_ ( NTP4VCMid A B )
          /\
          (
            ( NTP4VCMid A B ) <_ ( # ` C )
            /\
            ( # ` C ) = ( # ` D )
          )
        )
      )
    )
    /\
    (
      NTP4VCAllFirst
        C D A ( NTP4VCMid A B ) B E F G
    )
  )
) $.

ntp4vc-mergesort-rec-vc-definition $a |- (
  NTP4VCMergesortRecVC A B C D E F G
) <->
(
  (
    ( B - 1 ) <_ A
    /\
    ( NTP4VCBase C A B E F G )
  )
  \/
  (
    -. ( B - 1 ) <_ A
    /\
    ( NTP4VCRecursive A B C D E F G )
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

  $( Source theorem parameters A=l, B=r, C=a, and D=tmp. $)
  ntp4vc-l-integer $e |- A e. ZZ $.
  ntp4vc-r-integer $e |- B e. ZZ $.
  ntp4vc-a-word $e |- C e. Word U $.
  ntp4vc-tmp-word $e |- D e. Word U $.

  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- A <_ B $.
  ntp4vc-fact2 $e |- B <_ ( # ` C ) $.
  ntp4vc-fact3 $e |- ( # ` C ) = ( # ` D ) $.

  ntp4vc-pearl-top-down-mergesort-mergesort-rec-vc $a |- (
    NTP4VCMergesortRecVC A B C D U R G
  ) $.
$}
