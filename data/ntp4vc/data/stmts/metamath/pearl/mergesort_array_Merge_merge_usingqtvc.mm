$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/mergesort_array_Merge_merge_usingqtvc: the merge verification
  condition states that two adjacent sorted list segments either are already
  ordered or satisfy the copied-buffer and continuation contracts needed to
  obtain a sorted permutation of the merged segment. This file contains no
  proof.
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
  selected slices. NTP4VCSortedSub uses R at every pair of source integer
  indices in the indicated half-open interval.

  NTP4VCOutside, NTP4VCCopySegment, NTP4VCMergeOutcome, and
  NTP4VCTmpObligation factor the two universally quantified continuation
  contracts without changing their scopes. NTP4VCIdentityResult is the
  source already-merged conclusion. Source let-bound values are substituted
  by m - 1 and r - l, and proposition-valued conditionals are represented by
  equivalent exhaustive guarded disjunctions. The Boolean source value o1 is
  represented by { 0 , 1 }, with false = 0 and true = 1. The final declaration
  is Metamath's native unproved $a statement encoding; this statement file
  introduces no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCNatSub NTP4VCMin
  NTP4VCSliceStart NTP4VCSliceLen NTP4VCSlice NTP4VCAt
  NTP4VCPerm NTP4VCPermutSub NTP4VCSortedSub
  NTP4VCOutside NTP4VCCopySegment NTP4VCIdentityResult
  NTP4VCMergeOutcome NTP4VCTmpObligation NTP4VCMergeUsingVC
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
ntp4vc-outside-syntax
  $a wff ( NTP4VCOutside A B C D E F ) $.
ntp4vc-copy-segment-syntax
  $a wff ( NTP4VCCopySegment A B C D E F ) $.
ntp4vc-identity-result-syntax
  $a wff ( NTP4VCIdentityResult A B C D E F ) $.
ntp4vc-merge-outcome-syntax
  $a wff ( NTP4VCMergeOutcome A B C D E F G H ) $.
ntp4vc-tmp-obligation-syntax
  $a wff ( NTP4VCTmpObligation A B C D E F G H I ) $.
ntp4vc-merge-using-vc-syntax
  $a wff ( NTP4VCMergeUsingVC A B C D E F G H I ) $.

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

${
  $d i A B C D E F $.

  ntp4vc-copy-segment-definition $a |- (
    NTP4VCCopySegment A B C D E F
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
          C <_ i
          /\
          i < ( C + D )
        )
        ->
        (
          NTP4VCAt A i F
        )
        =
        (
          NTP4VCAt B ( ( C + i ) - C ) F
        )
      )
  ) $.
$}

ntp4vc-identity-result-definition $a |- (
  NTP4VCIdentityResult A B C D E F
) <->
(
  ( NTP4VCSortedSub A B C D E F )
  /\
  (
    NTP4VCPermutSub
      A A
      ( NTP4VCToNat B )
      ( NTP4VCToNat C )
      D
  )
) $.

${
  $d b A B C D E F G H $.

  ntp4vc-merge-outcome-definition $a |- (
    NTP4VCMergeOutcome A B C D E F G H
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
              E <_ ( # ` A )
              /\
              ( # ` A ) = ( # ` B )
            )
          )
        )
      )
      /\
      (
        ( NTP4VCSortedSub A C D F G H )
        /\
        ( NTP4VCSortedSub A D E F G H )
      )
    )
    /\
    A. b e. Word F
      (
        ( # ` b ) = ( # ` B )
        ->
        (
          (
            (
              ( NTP4VCSortedSub b C E F G H )
              /\
              (
                NTP4VCPermutSub
                  A b
                  ( NTP4VCToNat C )
                  ( NTP4VCToNat E )
                  F
              )
            )
            /\
            ( NTP4VCOutside b B C E F H )
          )
          ->
          (
            (
              ( NTP4VCSortedSub b C E F G H )
              /\
              (
                NTP4VCPermutSub
                  B b
                  ( NTP4VCToNat C )
                  ( NTP4VCToNat E )
                  F
              )
            )
            /\
            ( NTP4VCOutside b B C E F H )
          )
        )
      )
  ) $.
$}

${
  $d b A B C D E F G H I $.

  ntp4vc-tmp-obligation-definition $a |- (
    NTP4VCTmpObligation A B C D E F G H I
  ) <->
  (
    (
      (
        (
          0 <_ C
          /\
          (
            0 <_ F
            /\
            ( C + F ) <_ ( # ` B )
          )
        )
        /\
        (
          0 <_ C
          /\
          ( C + F ) <_ ( # ` A )
        )
      )
      /\
      A. b e. Word G
        (
          ( # ` b ) = ( # ` A )
          ->
          (
            (
              ( NTP4VCOutside b A C ( C + F ) G I )
              /\
              ( NTP4VCCopySegment b B C F G I )
            )
            ->
            (
              NTP4VCMergeOutcome
                b B C D E G H I
            )
          )
        )
    )
  ) $.
$}

ntp4vc-merge-using-vc-definition $a |- (
  NTP4VCMergeUsingVC A B C D E F G H I
) <->
(
  (
    F = 1
    /\
    (
      (
        0 <_ B
        /\
        B < ( # ` E )
      )
      /\
      (
        (
          0 <_ ( B - 1 )
          /\
          ( B - 1 ) < ( # ` E )
        )
        /\
        (
          (
            <.
              ( NTP4VCAt E ( B - 1 ) I ) ,
              ( NTP4VCAt E B I )
            >. e. H
            /\
            (
              NTP4VCIdentityResult
                E A C G H I
            )
          )
          \/
          (
            -.
            (
              <.
                ( NTP4VCAt E ( B - 1 ) I ) ,
                ( NTP4VCAt E B I )
              >. e. H
            )
            /\
            (
              NTP4VCTmpObligation
                D E A B C ( C - A ) G H I
            )
          )
        )
      )
    )
  )
  \/
  (
    -. F = 1
    /\
    (
      NTP4VCIdentityResult
        E A C G H I
    )
  )
) $.

${
  $d x y z A B C D E F G R U $.

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

  $( Source theorem parameters A=l, B=m, C=r, E=tmp, F=a, and G=o1. $)
  ntp4vc-l-integer $e |- A e. ZZ $.
  ntp4vc-m-integer $e |- B e. ZZ $.
  ntp4vc-r-integer $e |- C e. ZZ $.
  ntp4vc-tmp-word $e |- E e. Word U $.
  ntp4vc-a-word $e |- F e. Word U $.
  ntp4vc-o1-boolean $e |- G e. { 0 , 1 } $.

  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- A <_ B $.
  ntp4vc-fact2 $e |- B <_ C $.
  ntp4vc-fact3 $e |- C <_ ( # ` E ) $.
  ntp4vc-fact4 $e |- ( # ` E ) = ( # ` F ) $.
  ntp4vc-fact5 $e |- (
    NTP4VCSortedSub F A B U R D
  ) $.
  ntp4vc-fact6 $e |- (
    NTP4VCSortedSub F B C U R D
  ) $.
  ntp4vc-fact7 $e |- G = if (
    A < B ,
    if ( B < C , 1 , 0 ) ,
    0
  ) $.

  ntp4vc-pearl-mergesort-array-merge-using-vc $a |- (
    NTP4VCMergeUsingVC
      A B C E F G U R D
  ) $.
$}
