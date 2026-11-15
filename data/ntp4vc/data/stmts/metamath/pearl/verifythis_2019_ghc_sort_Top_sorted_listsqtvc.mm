$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc
  (ntp4vc__metamath__pearl/verifythis_2019_ghc_sort_Top_sorted_listsqtvc):
  the recursive sorted-segment-list verification condition preserves
  cutpoint bounds, ordering, segment monotonicity, exact integer
  multiplicities, and nondecreasing output lists. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer arrays and lists. NTP4VCToNat
  and NTP4VCAt reproduce the exported Int.toNat and totalized list lookup
  with default zero. NTP4VCOcc and NTP4VCCount are the source half-open map
  occurrence count and finite-list multiplicity.

  The source list_seq record has list and seq fields, invariant
  seq = reverse list, and extensional equality by those fields. It is
  represented bijectively by Word ZZ itself: the word is the list field and
  NTP4VCReverse of the word is the seq field. NTP4VCTail is the source list
  tail, while NTP4VCPrefixSeq is the source sequence slice
  seq[0 .. length(seq)-1].

  The strict-increasing, nondecreasing, and nonincreasing predicates are
  bidirectionally equivalent to the three source inductive sorted-list
  predicates on finite integer lists. NTP4VCPerm compares equal lengths and
  every integer multiplicity, equivalently finite-list permutation.
  NTP4VCFoldConcat uses an internal right-fold trace and is definitionally
  equivalent to fold_right (++) over a finite list of finite lists.

  Expanding the remaining biconditional definitions recovers both source
  list-match branches, every internal list, list_seq, result, and recursive
  result quantifier, all generated slicing and recursive-call obligations,
  and the complete two-part postcondition. The final declaration is
  Metamath's native unproved $a statement encoding; every auxiliary $a is
  syntax or a faithful explicit definition, and this database has no $p
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCReverse NTP4VCSeqAt
  NTP4VCTail NTP4VCPrefixSeq NTP4VCOrder
  NTP4VCOcc NTP4VCCount
  NTP4VCStrictSegment NTP4VCDecreasingSegment NTP4VCMonotone
  NTP4VCStrictIncreasing NTP4VCNondecreasing NTP4VCNonincreasing
  NTP4VCPerm NTP4VCBounds NTP4VCSegments NTP4VCOrdered
  NTP4VCFoldConcat NTP4VCAllSorted NTP4VCSegmentOccurrences
  NTP4VCListFromSpec NTP4VCSliceBounds NTP4VCPrefixFacts
  NTP4VCRecursiveInput NTP4VCRecursiveStep NTP4VCMatchSafety
  NTP4VCResultPremise NTP4VCFinalPost NTP4VCSortedListsVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-seq-at-syntax
  $a class ( NTP4VCSeqAt A B ) $.
ntp4vc-tail-syntax
  $a class ( NTP4VCTail A ) $.
ntp4vc-prefix-seq-syntax
  $a class ( NTP4VCPrefixSeq A ) $.
ntp4vc-order-syntax
  $a class ( NTP4VCOrder A ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B C D ) $.
ntp4vc-count-syntax
  $a class ( NTP4VCCount A B ) $.

ntp4vc-strict-segment-syntax
  $a wff ( NTP4VCStrictSegment A B C ) $.
ntp4vc-decreasing-segment-syntax
  $a wff ( NTP4VCDecreasingSegment A B C ) $.
ntp4vc-monotone-syntax
  $a wff ( NTP4VCMonotone A B C ) $.
ntp4vc-strict-increasing-syntax
  $a wff ( NTP4VCStrictIncreasing A ) $.
ntp4vc-nondecreasing-syntax
  $a wff ( NTP4VCNondecreasing A ) $.
ntp4vc-nonincreasing-syntax
  $a wff ( NTP4VCNonincreasing A ) $.
ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-bounds-syntax
  $a wff ( NTP4VCBounds A B ) $.
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
ntp4vc-list-from-spec-syntax
  $a wff ( NTP4VCListFromSpec A B C D ) $.
ntp4vc-slice-bounds-syntax
  $a wff ( NTP4VCSliceBounds A ) $.
ntp4vc-prefix-facts-syntax
  $a wff ( NTP4VCPrefixFacts A ) $.
ntp4vc-recursive-input-syntax
  $a wff ( NTP4VCRecursiveInput A B C ) $.
ntp4vc-recursive-step-syntax
  $a wff ( NTP4VCRecursiveStep A B C ) $.
ntp4vc-match-safety-syntax
  $a wff ( NTP4VCMatchSafety A B ) $.
ntp4vc-result-premise-syntax
  $a wff ( NTP4VCResultPremise A B C ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C ) $.
ntp4vc-sorted-lists-vc-syntax
  $a wff ( NTP4VCSortedListsVC A B ) $.

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
  $d i A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    i e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( A ` ( i + 1 ) )
  ) $.
$}

${
  $d i A $.

  ntp4vc-prefix-seq-definition $a |- (
    NTP4VCPrefixSeq A
  ) = (
    i e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( NTP4VCSeqAt A i )
  ) $.
$}

ntp4vc-order-definition $a |- (
  NTP4VCOrder A
) = if (
  ( # ` A ) < 2 ,
  A ,
  if (
    ( A ` 0 ) < ( A ` 1 ) ,
    A ,
    ( NTP4VCReverse A )
  )
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
  $d k A B $.

  ntp4vc-count-definition $a |- (
    NTP4VCCount A B
  ) = (
    # `
    { k e. ( 0 ..^ ( # ` A ) ) |
      ( A ` k ) = B
    }
  ) $.
$}

${
  $d x y A B C $.

  ntp4vc-strict-segment-definition $a |- (
    NTP4VCStrictSegment A B C
  ) <->
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
    ) $.
$}

${
  $d x y A B C $.

  ntp4vc-decreasing-segment-definition $a |- (
    NTP4VCDecreasingSegment A B C
  ) <->
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
    ) $.
$}

ntp4vc-monotone-definition $a |- (
  NTP4VCMonotone A B C
) <->
(
  ( NTP4VCStrictSegment A B C )
  \/
  ( NTP4VCDecreasingSegment A B C )
) $.

${
  $d i j A $.

  ntp4vc-strict-increasing-definition $a |- (
    NTP4VCStrictIncreasing A
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
        ( NTP4VCAt A i ) < ( NTP4VCAt A j )
      )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-nondecreasing-definition $a |- (
    NTP4VCNondecreasing A
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
  $d i j A $.

  ntp4vc-nonincreasing-definition $a |- (
    NTP4VCNonincreasing A
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
        ( NTP4VCAt A j ) <_ ( NTP4VCAt A i )
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
          ( NTP4VCCount A x )
          =
          ( NTP4VCCount B x )
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
      ( NTP4VCNondecreasing l )
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
          ( NTP4VCCount f x )
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
  $d x z A B C D $.

  ntp4vc-list-from-spec-definition $a |- (
    NTP4VCListFromSpec A B C D
  ) <->
  (
    A. x e. ZZ
      (
        ( NTP4VCCount A x )
        =
        ( NTP4VCOcc B x C D )
      )
    /\
    (
      A. x e. ZZ
        (
          x e. ran A
          ->
          E. z e. ZZ
            (
              (
                C <_ z
                /\
                z < D
              )
              /\
              ( NTP4VCAt B z ) = x
            )
        )
      /\
      (
        (
          ( NTP4VCStrictSegment B C D )
          ->
          ( NTP4VCStrictIncreasing A )
        )
        /\
        (
          (
            ( NTP4VCDecreasingSegment B C D )
            ->
            ( NTP4VCNonincreasing A )
          )
          /\
          (
            ( NTP4VCStrictIncreasing A )
            \/
            ( NTP4VCNonincreasing A )
          )
        )
      )
    )
  ) $.
$}

ntp4vc-slice-bounds-definition $a |- (
  NTP4VCSliceBounds A
) <->
(
  0 <_ 0
  /\
  (
    0 <_ ( ( # ` A ) - 1 )
    /\
    (
      ( ( # ` A ) - 1 )
      <_
      ( # ` ( NTP4VCReverse A ) )
    )
  )
) $.

${
  $d k A $.

  ntp4vc-prefix-facts-definition $a |- (
    NTP4VCPrefixFacts A
  ) <->
  (
    (
      # ` ( NTP4VCPrefixSeq A )
    ) = (
      ( ( # ` A ) - 1 ) - 0
    )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( ( ( # ` A ) - 1 ) - 0 )
        )
        ->
        (
          NTP4VCAt
            ( NTP4VCPrefixSeq A )
            k
        )
        =
        (
          NTP4VCSeqAt A ( 0 + k )
        )
      )
  ) $.
$}

ntp4vc-recursive-input-definition $a |- (
  NTP4VCRecursiveInput A B C
) <->
(
  ( NTP4VCTail A ) = C
  /\
  (
    0 < ( # ` C )
    /\
    (
      ( NTP4VCOrdered C )
      /\
      (
        ( NTP4VCBounds C ( # ` B ) )
        /\
        ( NTP4VCSegments B C )
      )
    )
  )
) $.

${
  $d l o A B C $.

  ntp4vc-recursive-step-definition $a |- (
    NTP4VCRecursiveStep A B C
  ) <->
  (
    ( NTP4VCSliceBounds A )
    /\
    (
      ( NTP4VCPrefixFacts A )
      ->
      (
        (
          NTP4VCPrefixSeq A
        ) = (
          NTP4VCReverse ( NTP4VCTail A )
        )
        /\
        A. l e. Word ZZ
          (
            (
              l = ( NTP4VCTail A )
              /\
              (
                NTP4VCReverse l
              ) = (
                NTP4VCPrefixSeq A
              )
            )
            ->
            (
              ( NTP4VCRecursiveInput A B l )
              /\
              A. o e. Word ( Word ZZ )
                (
                  (
                    ( NTP4VCAllSorted o )
                    /\
                    ( NTP4VCSegmentOccurrences o B l )
                  )
                  ->
                  (
                    ( NTP4VCStrictIncreasing C )
                    \/
                    ( NTP4VCNonincreasing C )
                  )
                )
            )
          )
      )
    )
  ) $.
$}

${
  $d q A B $.

  ntp4vc-match-safety-definition $a |- (
    NTP4VCMatchSafety A B
  ) <->
  (
    ( # ` A ) < 2
    \/
    (
      2 <_ ( # ` A )
      /\
      (
        (
          0 <_ ( A ` 1 )
          /\
          ( A ` 1 ) <_ ( # ` B )
        )
        /\
        (
          (
            0 <_ ( A ` 0 )
            /\
            ( A ` 0 ) <_ ( # ` B )
          )
          /\
          (
            ( NTP4VCMonotone B ( A ` 1 ) ( A ` 0 ) )
            /\
            A. q e. Word ZZ
              (
                (
                  NTP4VCListFromSpec
                    q B ( A ` 1 ) ( A ` 0 )
                )
                ->
                ( NTP4VCRecursiveStep A B q )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d l o q A B C $.

  ntp4vc-result-premise-definition $a |- (
    NTP4VCResultPremise A B C
  ) <->
  (
    (
      ( # ` A ) < 2
      /\
      C = (/)
    )
    \/
    (
      2 <_ ( # ` A )
      /\
      E. q e. Word ZZ
        (
          (
            NTP4VCListFromSpec
              q B ( A ` 1 ) ( A ` 0 )
          )
          /\
          (
            ( NTP4VCPrefixFacts A )
            /\
            E. l e. Word ZZ
              (
                (
                  l = ( NTP4VCTail A )
                  /\
                  (
                    NTP4VCReverse l
                  ) = (
                    NTP4VCPrefixSeq A
                  )
                )
                /\
                E. o e. Word ( Word ZZ )
                  (
                    (
                      ( NTP4VCAllSorted o )
                      /\
                      ( NTP4VCSegmentOccurrences o B l )
                    )
                    /\
                    (
                      (
                        ( NTP4VCNondecreasing ( NTP4VCOrder q ) )
                        /\
                        ( NTP4VCPerm q ( NTP4VCOrder q ) )
                      )
                      /\
                      C
                      =
                      (
                        <" ( NTP4VCOrder q ) ">
                        ++
                        o
                      )
                    )
                  )
              )
          )
        )
    )
  ) $.
$}

ntp4vc-final-post-definition $a |- (
  NTP4VCFinalPost A B C
) <->
(
  ( NTP4VCAllSorted C )
  /\
  ( NTP4VCSegmentOccurrences C B A )
) $.

${
  $d r A B $.

  ntp4vc-sorted-lists-vc-definition $a |- (
    NTP4VCSortedListsVC A B
  ) <->
  (
    ( NTP4VCMatchSafety A B )
    /\
    A. r e. Word ( Word ZZ )
      (
        ( NTP4VCResultPremise A B r )
        ->
        ( NTP4VCFinalPost A B r )
      )
  ) $.
$}

${
  $d f i j k l o q r s x y z A B $.

  $( Source theorem parameters: A=cutp and B=s. $)
  ntp4vc-cutp-list-seq $e |- A e. Word ZZ $.
  ntp4vc-s-integer-list $e |- B e. Word ZZ $.

  ntp4vc-cutp-nonempty $e |- 0 < ( # ` A ) $.
  ntp4vc-cutp-ordered $e |- ( NTP4VCOrdered A ) $.
  ntp4vc-cutp-bounds $e |- ( NTP4VCBounds A ( # ` B ) ) $.
  ntp4vc-cutp-segments $e |- ( NTP4VCSegments B A ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-top-sorted-lists-vc
    $a |- ( NTP4VCSortedListsVC A B ) $.
$}
