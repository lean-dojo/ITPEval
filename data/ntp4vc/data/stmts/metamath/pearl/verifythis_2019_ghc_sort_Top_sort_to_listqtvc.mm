$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc
  (ntp4vc__metamath__pearl/verifythis_2019_ghc_sort_Top_sort_to_listqtvc):
  the sort-to-list verification condition carries ordered monotonic
  cutpoints through sorted segment lists and a permutation result with the
  input list's exact integer occurrences and length. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer arrays and lists. NTP4VCToNat
  and NTP4VCAt reproduce the exported Int.toNat and totalized lookup with
  default zero. NTP4VCOcc is the exact map-occurrence cardinality on an
  arbitrary half-open integer interval.

  The source list_seq record has list and seq fields with invariant
  seq = reverse list and extensional equality by those fields. It is
  represented bijectively by Word ZZ itself: the word is the list field and
  NTP4VCReverse of the word is the seq field. Thus every source list_seq and
  no additional value is represented.

  NTP4VCFoldConcat is the source fold_right (++) over a finite list of finite
  integer lists. Its internal accumulator trace has one more entry than the
  outer list, ends in the empty word, and satisfies the right-fold recurrence
  at every index. This trace exists uniquely, so guarded quantification over
  its result is definitionally equivalent to using the source fold function.

  NTP4VCSorted is equivalent in both directions to the source inductive
  nondecreasing-list predicate. NTP4VCPerm uses equal length and equal
  multiplicity for every integer, which is equivalent in both directions to
  permutation of finite integer lists. Expanding the remaining biconditional
  definitions recovers every source domain, quantifier scope, assumption,
  implication, and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; every auxiliary $a is syntax or a faithful
  definition, and this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCReverse NTP4VCSeqAt NTP4VCOcc
  NTP4VCSorted NTP4VCPerm NTP4VCBounds NTP4VCMonotone
  NTP4VCSegments NTP4VCOrdered NTP4VCFoldConcat NTP4VCAllSorted
  NTP4VCSegmentOccurrences NTP4VCResultSpec NTP4VCMergeResults
  NTP4VCSortedLists NTP4VCCutpointHypotheses
  NTP4VCCutpointConclusion NTP4VCSortToListVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-seq-at-syntax
  $a class ( NTP4VCSeqAt A B ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B C D ) $.

ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-bounds-syntax
  $a wff ( NTP4VCBounds A B ) $.
ntp4vc-monotone-syntax
  $a wff ( NTP4VCMonotone A B C ) $.
ntp4vc-segments-syntax
  $a wff ( NTP4VCSegments A B ) $.
ntp4vc-ordered-syntax
  $a wff ( NTP4VCOrdered A ) $.
ntp4vc-fold-concat-syntax
  $a wff ( NTP4VCFoldConcat A B ) $.
ntp4vc-all-sorted-syntax
  $a wff ( NTP4VCAllSorted A ) $.
ntp4vc-segment-occurrences-syntax
  $a wff ( NTP4VCSegmentOccurrences A B C ) $.
ntp4vc-result-spec-syntax
  $a wff ( NTP4VCResultSpec A B ) $.
ntp4vc-merge-results-syntax
  $a wff ( NTP4VCMergeResults A B ) $.
ntp4vc-sorted-lists-syntax
  $a wff ( NTP4VCSortedLists A B ) $.
ntp4vc-cutpoint-hypotheses-syntax
  $a wff ( NTP4VCCutpointHypotheses A B ) $.
ntp4vc-cutpoint-conclusion-syntax
  $a wff ( NTP4VCCutpointConclusion A B ) $.
ntp4vc-sort-to-list-vc-syntax
  $a wff ( NTP4VCSortToListVC A ) $.

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
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

ntp4vc-seq-at-definition $a |- (
  NTP4VCSeqAt A B
) = (
  NTP4VCAt ( NTP4VCReverse A ) B
) $.

${
  $d k A B C D $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B C D
  ) = (
    # `
    { k e. ZZ |
      (
        (
          C <_ k
          /\
          k < D
        )
        /\
        ( NTP4VCAt A k ) = B
      )
    }
  ) $.
$}

${
  $d i j A $.

  ntp4vc-sorted-definition $a |- (
    NTP4VCSorted A
  ) <->
  (
    A e. Word ZZ
    /\
    A. i e. ZZ A. j e. ZZ
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
        ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
      )
  ) $.
$}

${
  $d x A B $.

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
      A. x e. ZZ
        (
          ( NTP4VCOcc A x 0 ( # ` A ) )
          =
          ( NTP4VCOcc B x 0 ( # ` B ) )
        )
    )
  ) $.
$}

${
  $d z A B $.

  ntp4vc-bounds-definition $a |- (
    NTP4VCBounds A B
  ) <->
  A. z e. ran A
    (
      0 <_ z
      /\
      z <_ B
    ) $.
$}

${
  $d x y A B C $.

  ntp4vc-monotone-definition $a |- (
    NTP4VCMonotone A B C
  ) <->
  (
    A. x e. ZZ A. y e. ZZ
      (
        (
          B <_ x
          /\
          (
            x < y
            /\
            y < C
          )
        )
        ->
        ( NTP4VCAt A x ) < ( NTP4VCAt A y )
      )
    \/
    A. x e. ZZ A. y e. ZZ
      (
        (
          B <_ x
          /\
          (
            x < y
            /\
            y < C
          )
        )
        ->
        ( NTP4VCAt A y ) <_ ( NTP4VCAt A x )
      )
  ) $.
$}

${
  $d k A B $.

  ntp4vc-segments-definition $a |- (
    NTP4VCSegments A B
  ) <->
  A. k e. ZZ
    (
      (
        0 <_ k
        /\
        k < ( ( # ` B ) - 1 )
      )
      ->
      (
        NTP4VCMonotone
          A
          ( NTP4VCSeqAt B k )
          ( NTP4VCSeqAt B ( k + 1 ) )
      )
    ) $.
$}

${
  $d i j A $.

  ntp4vc-ordered-definition $a |- (
    NTP4VCOrdered A
  ) <->
  A. i e. ZZ A. j e. ZZ
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
      ( NTP4VCSeqAt A i ) <_ ( NTP4VCSeqAt A j )
    ) $.
$}

${
  $d i s A B $.

  ntp4vc-fold-concat-definition $a |- (
    NTP4VCFoldConcat A B
  ) <->
  (
    (
      A e. Word ( Word ZZ )
      /\
      B e. Word ZZ
    )
    /\
    E. s e. Word ( Word ZZ )
      (
        ( # ` s ) = ( ( # ` A ) + 1 )
        /\
        (
          ( s ` ( # ` A ) ) = (/)
          /\
          (
            ( s ` 0 ) = B
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( s ` i )
                =
                (
                  ( A ` i )
                  ++
                  ( s ` ( i + 1 ) )
                )
              )
          )
        )
      )
  ) $.
$}

${
  $d l A $.

  ntp4vc-all-sorted-definition $a |- (
    NTP4VCAllSorted A
  ) <->
  (
    A e. Word ( Word ZZ )
    /\
    A. l e. ran A
      ( NTP4VCSorted l )
  ) $.
$}

${
  $d f x A B C $.

  ntp4vc-segment-occurrences-definition $a |- (
    NTP4VCSegmentOccurrences A B C
  ) <->
  A. f e. Word ZZ
    (
      ( NTP4VCFoldConcat A f )
      ->
      A. x e. ZZ
        (
          ( NTP4VCOcc f x 0 ( # ` f ) )
          =
          (
            NTP4VCOcc
              B x
              ( NTP4VCSeqAt C 0 )
              ( NTP4VCSeqAt C ( ( # ` C ) - 1 ) )
          )
        )
    ) $.
$}

${
  $d x A B $.

  ntp4vc-result-spec-definition $a |- (
    NTP4VCResultSpec A B
  ) <->
  (
    ( NTP4VCSorted A )
    /\
    (
      A. x e. ZZ
        (
          ( NTP4VCOcc B x 0 ( # ` B ) )
          =
          ( NTP4VCOcc A x 0 ( # ` A ) )
        )
      /\
      ( # ` A ) = ( # ` B )
    )
  ) $.
$}

${
  $d f r A B $.

  ntp4vc-merge-results-definition $a |- (
    NTP4VCMergeResults A B
  ) <->
  A. f e. Word ZZ
    (
      ( NTP4VCFoldConcat A f )
      ->
      A. r e. Word ZZ
        (
          (
            ( NTP4VCSorted r )
            /\
            ( NTP4VCPerm r f )
          )
          ->
          ( NTP4VCResultSpec r B )
        )
    ) $.
$}

${
  $d q A B $.

  ntp4vc-sorted-lists-definition $a |- (
    NTP4VCSortedLists A B
  ) <->
  A. q e. Word ( Word ZZ )
    (
      (
        ( NTP4VCAllSorted q )
        /\
        ( NTP4VCSegmentOccurrences q A B )
      )
      ->
      (
        ( NTP4VCAllSorted q )
        /\
        ( NTP4VCMergeResults q A )
      )
    ) $.
$}

ntp4vc-cutpoint-hypotheses-definition $a |- (
  NTP4VCCutpointHypotheses A B
) <->
(
  ( NTP4VCSeqAt B 0 ) = 0
  /\
  (
    ( NTP4VCSeqAt B ( ( # ` B ) - 1 ) ) = ( # ` A )
    /\
    (
      2 <_ ( # ` B )
      /\
      (
        ( NTP4VCBounds B ( # ` A ) )
        /\
        (
          ( NTP4VCSegments A B )
          /\
          ( NTP4VCOrdered B )
        )
      )
    )
  )
) $.

ntp4vc-cutpoint-conclusion-definition $a |- (
  NTP4VCCutpointConclusion A B
) <->
(
  0 < ( # ` B )
  /\
  (
    ( NTP4VCOrdered B )
    /\
    (
      ( NTP4VCBounds B ( # ` A ) )
      /\
      (
        ( NTP4VCSegments A B )
        /\
        ( NTP4VCSortedLists A B )
      )
    )
  )
) $.

${
  $d b A $.

  ntp4vc-sort-to-list-vc-definition $a |- (
    NTP4VCSortToListVC A
  ) <->
  (
    0 < ( # ` A )
    /\
    A. b e. Word ZZ
      (
        ( NTP4VCCutpointHypotheses A b )
        ->
        ( NTP4VCCutpointConclusion A b )
      )
  ) $.
$}

${
  $d b f i j k l q r s x y z A $.

  ntp4vc-input-list $e |- A e. Word ZZ $.
  ntp4vc-input-nonempty $e |- 0 < ( # ` A ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-top-sort-to-list-vc
    $a |- ( NTP4VCSortToListVC A ) $.
$}
