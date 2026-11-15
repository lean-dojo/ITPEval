$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_copy_listqtvc: the list-to-array copy
  verification condition lifts the recursive tail copy, frame, and occurrence
  postconditions after writing the head at the starting index. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer lists. NTP4VCToNat reproduces
  Int.toNat, NTP4VCAt is integer-indexed lookup with default zero outside
  [0, length), and NTP4VCSet, NTP4VCNth, and NTP4VCFunUpdate reproduce
  List.set, integer-indexed lookup, and Function.update.

  NTP4VCOcc is the cardinality of positions having a specified value in a
  half-open interval of integer indices; NTP4VCCount is the corresponding
  whole-list occurrence count. NTP4VCCopy, NTP4VCFrame, and NTP4VCOccPost are
  the three source postconditions. NTP4VCPost packages all three only where
  the source recursive and nonempty branches contain all three; the empty
  branch deliberately retains only the copy and occurrence conjuncts present
  in the generated verification condition.

  The source list match is represented by its exhaustive empty case and an
  internal existential head-tail decomposition of a nonempty word. Thus the
  recursive witnesses are not exposed as theorem parameters. Expanding the
  displayed biconditional definitions recovers the original integer and list
  domains, assumptions, branch structure, length and function-update
  implications, recursive precondition, universal intermediate-array
  quantifier, and complete conclusion. Every auxiliary $a declaration is
  syntax or a faithful definitional abbreviation; the final $a declaration
  is Metamath's native unproved statement encoding, and there is no $p
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCNth NTP4VCFunUpdate
  NTP4VCOcc NTP4VCCount NTP4VCCopy NTP4VCFrame NTP4VCOccPost
  NTP4VCPost NTP4VCNilBranch NTP4VCConsBranch NTP4VCCopyListVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.
ntp4vc-nth-syntax
  $a class ( NTP4VCNth A ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C ) $.
ntp4vc-occ-syntax
  $a class ( NTP4VCOcc A B C D ) $.
ntp4vc-count-syntax
  $a class ( NTP4VCCount A B ) $.

ntp4vc-copy-syntax
  $a wff ( NTP4VCCopy A B C ) $.
ntp4vc-frame-syntax
  $a wff ( NTP4VCFrame A B C ) $.
ntp4vc-occ-post-syntax
  $a wff ( NTP4VCOccPost A B C ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D ) $.
ntp4vc-nil-branch-syntax
  $a wff ( NTP4VCNilBranch A B C ) $.
ntp4vc-cons-branch-syntax
  $a wff ( NTP4VCConsBranch A B C D E ) $.
ntp4vc-copy-list-vc-syntax
  $a wff ( NTP4VCCopyListVC A B C ) $.

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
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
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
  $d k A $.

  ntp4vc-nth-definition $a |- (
    NTP4VCNth A
  ) = (
    k e. ZZ |->
      ( NTP4VCAt A k )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C
  ) = (
    k e. ZZ |->
      if (
        k = B ,
        C ,
        ( A ` k )
      )
  ) $.
$}

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
  $d x A B C $.

  ntp4vc-copy-definition $a |- (
    NTP4VCCopy A B C
  ) <->
  A. x e. ZZ
    (
      (
        C <_ x
        /\
        x < ( # ` A )
      )
      ->
      ( NTP4VCAt A x )
      =
      ( NTP4VCAt B ( x - C ) )
    ) $.
$}

${
  $d x A B C $.

  ntp4vc-frame-definition $a |- (
    NTP4VCFrame A B C
  ) <->
  A. x e. ZZ
    (
      (
        0 <_ x
        /\
        x < C
      )
      ->
      ( NTP4VCAt A x ) = ( NTP4VCAt B x )
    ) $.
$}

${
  $d x A B C $.

  ntp4vc-occ-post-definition $a |- (
    NTP4VCOccPost A B C
  ) <->
  A. x e. ZZ
    (
      NTP4VCOcc A x C ( # ` A )
    ) = (
      NTP4VCCount B x
    ) $.
$}

ntp4vc-post-definition $a |- (
  NTP4VCPost A B C D
) <->
(
  ( NTP4VCCopy A B D )
  /\
  (
    ( NTP4VCFrame A C D )
    /\
    ( NTP4VCOccPost A B D )
  )
) $.

ntp4vc-nil-branch-definition $a |- (
  NTP4VCNilBranch A B C
) <->
(
  ( NTP4VCCopy B A C )
  /\
  ( NTP4VCOccPost B A C )
) $.

${
  $d x A B C D E $.

  ntp4vc-cons-branch-definition $a |- (
    NTP4VCConsBranch A B C D E
  ) <->
  (
    (
      0 <_ A
      /\
      A < ( # ` C )
    )
    /\
    (
      (
        #
        `
        ( NTP4VCSet C A D )
      )
      =
      ( # ` C )
      ->
      (
        (
          NTP4VCNth ( NTP4VCSet C A D )
        )
        =
        (
          NTP4VCFunUpdate
            ( NTP4VCNth C )
            A
            D
        )
        ->
        (
          (
            E = E
            /\
            (
              0 <_ ( A + 1 )
              /\
              (
                ( # ` E )
                =
                (
                  ( # ` ( NTP4VCSet C A D ) )
                  -
                  ( A + 1 )
                )
              )
            )
          )
          /\
          A. x e. Word ZZ
            (
              (
                ( # ` x )
                =
                ( # ` ( NTP4VCSet C A D ) )
              )
              ->
              (
                ( NTP4VCPost
                  x E ( NTP4VCSet C A D ) ( A + 1 )
                )
                ->
                ( NTP4VCPost x B C A )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d h t A B C $.

  ntp4vc-copy-list-vc-definition $a |- (
    NTP4VCCopyListVC A B C
  ) <->
  (
    (
      B = (/) 
      /\
      ( NTP4VCNilBranch B C A )
    )
    \/
    E. h e. ZZ E. t e. Word ZZ
      (
        B = ( <" h "> ++ t )
        /\
        ( NTP4VCConsBranch A B C h t )
      )
  ) $.
$}

${
  $d h t x A B C $.

  $( Source theorem parameters: A=s, B=l, and C=a. $)
  ntp4vc-s-integer $e |- A e. ZZ $.
  ntp4vc-l-list $e |- B e. Word ZZ $.
  ntp4vc-a-list $e |- C e. Word ZZ $.

  ntp4vc-s-nonnegative $e |- 0 <_ A $.
  ntp4vc-length-relation $e |- (
    # ` B
  ) = (
    ( # ` C ) - A
  ) $.

  ntp4vc-pearl-verifythis-2019-ghc-sort-copy-list-vc $a |- (
    NTP4VCCopyListVC A B C
  ) $.
$}
