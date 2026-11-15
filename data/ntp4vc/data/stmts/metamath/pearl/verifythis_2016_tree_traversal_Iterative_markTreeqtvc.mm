$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc
  (ntp4vc__metamath__pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc):
  the iterative Morris-style binary-tree traversal verification condition
  preserves its explicit simulated call stack, decreases its integer
  variant, restores the tree pointers, and marks every tree node. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  L is an arbitrary nonempty location carrier and NTP4VCNull is its
  distinguished null location. Boolean, pointer-kind, and traversal-phase
  values are represented by exact finite tagged carriers. Memories, snapshots,
  and frames are full Cartesian products of the source total-function fields;
  consequently every source function and record value remains available.

  T and Q are exactly the finite inductive carriers of location-labelled
  binary trees and simulated call stacks. Their tagged constructors are
  disjoint and injective, and the scoped closure, exhaustiveness, and
  structural-induction hypotheses exclude both missing finite values and
  extraneous non-well-founded values. O is the exact option carrier over T.

  The scoped equations below are the complete recursive definitions of
  is_tree, footprint, tree size, is_stack, and stack_size. All remaining
  predicates and functions are literal set-theoretic definitions of the Why3
  source. Proposition-valued conditionals and datatype matches are expanded
  into equivalent guarded branches over exhaustive exact carriers. Repeated
  non-null facts, tautological safety implications, nested memory updates,
  all universal state quantifiers, and both strict variant decreases are
  retained. SetMM ZZ is the full unbounded integer domain. The final $a is
  Metamath's native unproved statement encoding; every preceding $a is syntax
  or a faithful definition, and this database contains no proof declaration.
$)

$c
  NTP4VCBool NTP4VCFalse NTP4VCTrue
  NTP4VCKind NTP4VCParent NTP4VCLeft NTP4VCRight
  NTP4VCPhase NTP4VCGoLeft NTP4VCGoRight NTP4VCGoBack NTP4VCFinish
  NTP4VCNull
  NTP4VCAccessors NTP4VCMarks NTP4VCMemory
  NTP4VCMemAccessor NTP4VCMemMark
  NTP4VCSnap NTP4VCSnapPointers NTP4VCSnapCursor
  NTP4VCSnapParent NTP4VCSnapMarks
  NTP4VCFrame NTP4VCMemo0 NTP4VCTreeField NTP4VCTLeft
  NTP4VCPLeft NTP4VCTRight NTP4VCPRight NTP4VCMemo1
  NTP4VCMemo2 NTP4VCMemo3 NTP4VCMemo4
  NTP4VCEmpty NTP4VCNode
  NTP4VCNone NTP4VCSome
  NTP4VCBottom NTP4VCRunning NTP4VCDone
  NTP4VCUpdate NTP4VCFootprint NTP4VCSize
  NTP4VCIsTree NTP4VCExt NTP4VCUnchanged NTP4VCWasMarked
  NTP4VCNextPhase NTP4VCRotated NTP4VCFrameMemo
  NTP4VCBlocRel NTP4VCRecRel NTP4VCIsStack NTP4VCStackSize
  NTP4VCCodePhase NTP4VCContinuation NTP4VCNextState
  NTP4VCResultCheck NTP4VCLeafBranch NTP4VCRotateBranch
  NTP4VCNonNullBranch NTP4VCTerminalBranch NTP4VCIteration
  NTP4VCOuterState NTP4VCMarkTreeVC
$.

ntp4vc-bool-syntax $a class NTP4VCBool $.
ntp4vc-false-syntax $a class NTP4VCFalse $.
ntp4vc-true-syntax $a class NTP4VCTrue $.
ntp4vc-kind-syntax $a class NTP4VCKind $.
ntp4vc-parent-kind-syntax $a class NTP4VCParent $.
ntp4vc-left-kind-syntax $a class NTP4VCLeft $.
ntp4vc-right-kind-syntax $a class NTP4VCRight $.
ntp4vc-phase-syntax $a class NTP4VCPhase $.
ntp4vc-go-left-syntax $a class NTP4VCGoLeft $.
ntp4vc-go-right-syntax $a class NTP4VCGoRight $.
ntp4vc-go-back-syntax $a class NTP4VCGoBack $.
ntp4vc-finish-syntax $a class NTP4VCFinish $.
ntp4vc-null-syntax $a class NTP4VCNull $.

ntp4vc-accessors-syntax $a class ( NTP4VCAccessors A ) $.
ntp4vc-marks-syntax $a class ( NTP4VCMarks A ) $.
ntp4vc-memory-syntax $a class ( NTP4VCMemory A ) $.
ntp4vc-mem-accessor-syntax $a class ( NTP4VCMemAccessor A ) $.
ntp4vc-mem-mark-syntax $a class ( NTP4VCMemMark A ) $.

ntp4vc-snap-syntax $a class ( NTP4VCSnap A ) $.
ntp4vc-snap-pointers-syntax $a class ( NTP4VCSnapPointers A ) $.
ntp4vc-snap-cursor-syntax $a class ( NTP4VCSnapCursor A ) $.
ntp4vc-snap-parent-syntax $a class ( NTP4VCSnapParent A ) $.
ntp4vc-snap-marks-syntax $a class ( NTP4VCSnapMarks A ) $.

ntp4vc-frame-syntax $a class ( NTP4VCFrame A B ) $.
ntp4vc-memo0-syntax $a class ( NTP4VCMemo0 A ) $.
ntp4vc-tree-field-syntax $a class ( NTP4VCTreeField A ) $.
ntp4vc-tleft-syntax $a class ( NTP4VCTLeft A ) $.
ntp4vc-pleft-syntax $a class ( NTP4VCPLeft A ) $.
ntp4vc-tright-syntax $a class ( NTP4VCTRight A ) $.
ntp4vc-pright-syntax $a class ( NTP4VCPRight A ) $.
ntp4vc-memo1-syntax $a class ( NTP4VCMemo1 A ) $.
ntp4vc-memo2-syntax $a class ( NTP4VCMemo2 A ) $.
ntp4vc-memo3-syntax $a class ( NTP4VCMemo3 A ) $.
ntp4vc-memo4-syntax $a class ( NTP4VCMemo4 A ) $.

ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.
ntp4vc-none-syntax $a class NTP4VCNone $.
ntp4vc-some-syntax $a class ( NTP4VCSome A ) $.
ntp4vc-bottom-syntax $a class NTP4VCBottom $.
ntp4vc-running-syntax $a class ( NTP4VCRunning A B C ) $.
ntp4vc-done-syntax $a class NTP4VCDone $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-footprint-syntax $a class ( NTP4VCFootprint A ) $.
ntp4vc-size-syntax $a class ( NTP4VCSize A ) $.
ntp4vc-is-tree-syntax $a wff ( NTP4VCIsTree A B C D ) $.
ntp4vc-ext-syntax $a wff ( NTP4VCExt A B C D ) $.
ntp4vc-unchanged-syntax $a wff ( NTP4VCUnchanged A B C ) $.
ntp4vc-was-marked-syntax $a wff ( NTP4VCWasMarked A B C D ) $.
ntp4vc-next-phase-syntax $a class ( NTP4VCNextPhase A ) $.
ntp4vc-rotated-syntax $a wff ( NTP4VCRotated A B C D E ) $.
ntp4vc-frame-memo-syntax $a class ( NTP4VCFrameMemo A B ) $.
ntp4vc-bloc-rel-syntax $a wff ( NTP4VCBlocRel A B C D E ) $.
ntp4vc-rec-rel-syntax $a wff ( NTP4VCRecRel A B C D ) $.
ntp4vc-is-stack-syntax
  $a wff ( NTP4VCIsStack A B C D E F ) $.
ntp4vc-stack-size-syntax $a class ( NTP4VCStackSize A ) $.
ntp4vc-code-phase-syntax $a class ( NTP4VCCodePhase A ) $.
ntp4vc-continuation-syntax $a wff (
  NTP4VCContinuation A B C D E F
) $.
ntp4vc-next-state-syntax $a wff (
  NTP4VCNextState A B C D E F G H I J K
) $.
ntp4vc-result-check-syntax $a wff (
  NTP4VCResultCheck A B
) $.
ntp4vc-leaf-branch-syntax $a wff (
  NTP4VCLeafBranch A B C D E F G H I
) $.
ntp4vc-rotate-branch-syntax $a wff (
  NTP4VCRotateBranch A B C D E F G H I
) $.
ntp4vc-non-null-branch-syntax $a wff (
  NTP4VCNonNullBranch A B C D E F G H I
) $.
ntp4vc-terminal-branch-syntax $a wff (
  NTP4VCTerminalBranch A B C D E F G H
) $.
ntp4vc-iteration-syntax $a wff (
  NTP4VCIteration A B C D E F G H I J K L
) $.
ntp4vc-outer-state-syntax $a wff (
  NTP4VCOuterState A B C D E F G H I
) $.
ntp4vc-mark-tree-vc-syntax $a wff (
  NTP4VCMarkTreeVC A B C D E F G
) $.

ntp4vc-bool-definition $a |- NTP4VCBool = ( 0 ..^ 2 ) $.
ntp4vc-false-definition $a |- NTP4VCFalse = 0 $.
ntp4vc-true-definition $a |- NTP4VCTrue = 1 $.
ntp4vc-kind-definition $a |- NTP4VCKind = ( 0 ..^ 3 ) $.
ntp4vc-parent-kind-definition $a |- NTP4VCParent = 0 $.
ntp4vc-left-kind-definition $a |- NTP4VCLeft = 1 $.
ntp4vc-right-kind-definition $a |- NTP4VCRight = 2 $.
ntp4vc-phase-definition $a |- NTP4VCPhase = ( 0 ..^ 4 ) $.
ntp4vc-go-left-definition $a |- NTP4VCGoLeft = 0 $.
ntp4vc-go-right-definition $a |- NTP4VCGoRight = 1 $.
ntp4vc-go-back-definition $a |- NTP4VCGoBack = 2 $.
ntp4vc-finish-definition $a |- NTP4VCFinish = 3 $.

ntp4vc-accessors-definition $a |- (
  NTP4VCAccessors A
) = ( ( A ^m A ) ^m NTP4VCKind ) $.

ntp4vc-marks-definition $a |- (
  NTP4VCMarks A
) = ( NTP4VCBool ^m A ) $.

ntp4vc-memory-definition $a |- (
  NTP4VCMemory A
) = ( ( NTP4VCAccessors A ) X. ( NTP4VCMarks A ) ) $.

ntp4vc-mem-accessor-definition $a |- (
  NTP4VCMemAccessor A
) = ( 1st ` A ) $.

ntp4vc-mem-mark-definition $a |- (
  NTP4VCMemMark A
) = ( 2nd ` A ) $.

ntp4vc-snap-definition $a |- (
  NTP4VCSnap A
) = (
  ( NTP4VCAccessors A )
  X. ( A X. ( A X. ( NTP4VCMarks A ) ) )
) $.

ntp4vc-snap-pointers-definition $a |- (
  NTP4VCSnapPointers A
) = ( 1st ` A ) $.

ntp4vc-snap-cursor-definition $a |- (
  NTP4VCSnapCursor A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-snap-parent-definition $a |- (
  NTP4VCSnapParent A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-snap-marks-definition $a |- (
  NTP4VCSnapMarks A
) = ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-frame-definition $a |- (
  NTP4VCFrame A B
) = (
  ( NTP4VCSnap A )
  X. (
    B X. (
      B X. (
        A X. (
          B X. (
            A X. (
              ( NTP4VCSnap A )
              X. (
                ( NTP4VCSnap A )
                X. (
                  ( NTP4VCSnap A )
                  X. ( NTP4VCSnap A )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-memo0-definition $a |- (
  NTP4VCMemo0 A
) = ( 1st ` A ) $.

ntp4vc-tree-field-definition $a |- (
  NTP4VCTreeField A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-tleft-definition $a |- (
  NTP4VCTLeft A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-pleft-definition $a |- (
  NTP4VCPLeft A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-tright-definition $a |- (
  NTP4VCTRight A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-pright-definition $a |- (
  NTP4VCPRight A
) = (
  1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
) $.

ntp4vc-memo1-definition $a |- (
  NTP4VCMemo1 A
) = (
  1st ` (
    2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
  )
) $.

ntp4vc-memo2-definition $a |- (
  NTP4VCMemo2 A
) = (
  1st ` (
    2nd ` (
      2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
    )
  )
) $.

ntp4vc-memo3-definition $a |- (
  NTP4VCMemo3 A
) = (
  1st ` (
    2nd ` (
      2nd ` (
        2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
      )
    )
  )
) $.

ntp4vc-memo4-definition $a |- (
  NTP4VCMemo4 A
) = (
  2nd ` (
    2nd ` (
      2nd ` (
        2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) )
      )
    )
  )
) $.

ntp4vc-empty-definition $a |- NTP4VCEmpty = <. 0 , (/) >. $.
ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.
ntp4vc-none-definition $a |- NTP4VCNone = <. 0 , (/) >. $.
ntp4vc-some-definition $a |- (
  NTP4VCSome A
) = <. 1 , A >. $.
ntp4vc-bottom-definition $a |- NTP4VCBottom = <. 0 , (/) >. $.
ntp4vc-running-definition $a |- (
  NTP4VCRunning A B C
) = <. 1 , <. A , <. B , C >. >. >. $.
ntp4vc-done-definition $a |- NTP4VCDone = <. 2 , (/) >. $.

${
  $d x A B C D $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. D |-> if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d k x A B C D $.

  ntp4vc-ext-definition $a |- (
    NTP4VCExt A B C D
  ) <-> (
    A. k e. NTP4VCKind A. x e. A
      (
        x e. B
        ->
        ( ( C ` k ) ` x ) = ( ( D ` k ) ` x )
      )
  ) $.
$}

${
  $d k x A B C $.

  ntp4vc-unchanged-definition $a |- (
    NTP4VCUnchanged A B C
  ) <-> (
    A. k e. NTP4VCKind A. x e. A
      ( ( B ` k ) ` x ) = ( ( C ` k ) ` x )
  ) $.
$}

${
  $d x A B C D $.

  ntp4vc-was-marked-definition $a |- (
    NTP4VCWasMarked A B C D
  ) <-> (
    (
      A. x e. A
        (
          x e. ( NTP4VCFootprint B )
          ->
          ( D ` x ) = NTP4VCTrue
        )
    )
    /\
    A. x e. A
      (
        -. x e. ( NTP4VCFootprint B )
        ->
        ( D ` x ) = ( C ` x )
      )
  ) $.
$}

ntp4vc-next-phase-definition $a |- (
  NTP4VCNextPhase A
) = if (
  A = NTP4VCGoLeft ,
  NTP4VCGoRight ,
  if (
    A = NTP4VCGoRight ,
    NTP4VCGoBack ,
    if (
      A = NTP4VCGoBack ,
      NTP4VCGoLeft ,
      NTP4VCFinish
    )
  )
) $.

${
  $d k x A B C D E $.

  ntp4vc-rotated-definition $a |- (
    NTP4VCRotated A B C D E
  ) <-> (
    (
      A. k e. NTP4VCKind A. x e. A
        (
          x =/= E
          ->
          ( ( B ` k ) ` x ) = ( ( C ` k ) ` x )
        )
    )
    /\
    (
      D =/= NTP4VCFinish
      ->
      E =/= NTP4VCNull
    )
    /\
    (
      (
        D = NTP4VCGoLeft
        ->
        ( NTP4VCUnchanged A B C )
      )
      /\
      (
        D = NTP4VCGoRight
        ->
        (
          ( ( C ` NTP4VCLeft ) ` E )
          =
          ( ( B ` NTP4VCRight ) ` E )
          /\
          (
            ( ( C ` NTP4VCRight ) ` E )
            =
            ( ( B ` NTP4VCParent ) ` E )
            /\
            ( ( C ` NTP4VCParent ) ` E )
            =
            ( ( B ` NTP4VCLeft ) ` E )
          )
        )
      )
      /\
      (
        D = NTP4VCGoBack
        ->
        (
          ( ( B ` NTP4VCLeft ) ` E )
          =
          ( ( C ` NTP4VCRight ) ` E )
          /\
          (
            ( ( B ` NTP4VCRight ) ` E )
            =
            ( ( C ` NTP4VCParent ) ` E )
            /\
            ( ( B ` NTP4VCParent ) ` E )
            =
            ( ( C ` NTP4VCLeft ) ` E )
          )
        )
      )
      /\
      (
        D = NTP4VCFinish
        ->
        E = NTP4VCNull
      )
    )
  ) $.
$}

ntp4vc-frame-memo-definition $a |- (
  NTP4VCFrameMemo A B
) = if (
  B <_ 0 ,
  ( NTP4VCMemo0 A ) ,
  if (
    B <_ 1 ,
    ( NTP4VCMemo1 A ) ,
    if (
      B <_ 2 ,
      ( NTP4VCMemo2 A ) ,
      if (
        B <_ 3 ,
        ( NTP4VCMemo3 A ) ,
        ( NTP4VCMemo4 A )
      )
    )
  )
) $.

${
  $d x A B C D E $.

  ntp4vc-bloc-rel-definition $a |- (
    NTP4VCBlocRel A B C D E
  ) <-> (
    ( NTP4VCSnapParent E ) = ( NTP4VCSnapCursor D )
    /\
    (
      ( NTP4VCSnapCursor E )
      =
      (
        (
          ( NTP4VCSnapPointers E ) ` NTP4VCParent
        )
        ` ( NTP4VCSnapParent E )
      )
    )
    /\
    (
      (
        ( NTP4VCSnapMarks E )
        ` ( NTP4VCSnapParent E )
      )
      =
      NTP4VCTrue
    )
    /\
    (
      A. x e. A
        (
          x =/= ( NTP4VCSnapParent E )
          ->
          (
            ( NTP4VCSnapMarks E ) ` x
          )
          =
          (
            ( NTP4VCSnapMarks D ) ` x
          )
        )
    )
    /\
    (
      (
        (
          (
            ( NTP4VCSnapPointers D ) ` NTP4VCLeft
          )
          ` ( NTP4VCSnapCursor D )
        )
        =
        NTP4VCNull
        /\
        NTP4VCNull
        =
        (
          (
            ( NTP4VCSnapPointers D ) ` NTP4VCRight
          )
          ` ( NTP4VCSnapCursor D )
        )
      )
      ->
      ( NTP4VCSnapPointers E ) = ( NTP4VCSnapPointers D )
    )
    /\
    (
      -.
      (
        (
          (
            ( NTP4VCSnapPointers D ) ` NTP4VCLeft
          )
          ` ( NTP4VCSnapCursor D )
        )
        =
        NTP4VCNull
        /\
        NTP4VCNull
        =
        (
          (
            ( NTP4VCSnapPointers D ) ` NTP4VCRight
          )
          ` ( NTP4VCSnapCursor D )
        )
      )
      ->
      (
        NTP4VCRotated
          A C
          ( NTP4VCSnapPointers E )
          ( NTP4VCNextPhase B )
          ( NTP4VCSnapParent E )
      )
    )
  ) $.
$}

ntp4vc-rec-rel-definition $a |- (
  NTP4VCRecRel A B C D
) <-> (
  ( NTP4VCUnchanged
      A
      ( NTP4VCSnapPointers C )
      ( NTP4VCSnapPointers D ) )
  /\
  (
    ( NTP4VCSnapCursor D ) = ( NTP4VCSnapParent C )
    /\
    (
      ( NTP4VCSnapParent D ) = ( NTP4VCSnapCursor C )
      /\
      (
        NTP4VCWasMarked
          A B
          ( NTP4VCSnapMarks C )
          ( NTP4VCSnapMarks D )
      )
    )
  )
) $.

ntp4vc-code-phase-definition $a |- (
  NTP4VCCodePhase A
) = if (
  A = 0 ,
  NTP4VCGoLeft ,
  if (
    A = 2 ,
    NTP4VCGoRight ,
    NTP4VCGoBack
  )
) $.

${
  $d f p s A B C D E F $.

  ntp4vc-continuation-definition $a |- (
    NTP4VCContinuation A B C D E F
  ) <-> (
    E. s e. C E. p e. ZZ E. f e. ( NTP4VCFrame A B )
      (
        D = ( NTP4VCRunning s p f )
        /\
        (
          NTP4VCBlocRel
            A
            ( NTP4VCCodePhase p )
            ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
            E F
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H I J K $.

  $(
    Arguments are L, T, Q, O, t, stop, previous snapshot, current stack,
    next snapshot, current memory, and the next cursor location.
  $)
  ntp4vc-next-state-definition $a |- (
    NTP4VCNextState A B C D E F G H I J K
  ) <-> (
    (
      ( NTP4VCIsStack A E F G H NTP4VCNone )
      /\
      ( NTP4VCContinuation A B C H G I )
    )
    /\
    A. x e. C
      (
        (
          ( NTP4VCIsStack A E F I x NTP4VCNone )
          /\
          ( NTP4VCStackSize x ) < ( NTP4VCStackSize H )
        )
        ->
        (
          (
            0 <_ ( NTP4VCStackSize H )
            /\
            ( NTP4VCStackSize x ) < ( NTP4VCStackSize H )
          )
          /\
          (
            K = NTP4VCNull
            ->
            T.
          )
          /\
          (
            ( NTP4VCSnapPointers I ) = ( NTP4VCMemAccessor J )
            /\
            (
              ( NTP4VCSnapCursor I ) = K
              /\
              (
                ( NTP4VCSnapParent I ) = ( NTP4VCSnapCursor G )
                /\
                (
                  ( NTP4VCSnapMarks I ) = ( NTP4VCMemMark J )
                  /\
                  ( NTP4VCIsStack A E F I x NTP4VCNone )
                )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d r A B $.

  ntp4vc-result-check-definition $a |- (
    NTP4VCResultCheck A B
  ) <-> (
    A. r e. NTP4VCBool
      (
        r
        =
        if (
          B = NTP4VCTrue ,
          if (
            ( NTP4VCSnapCursor A ) = NTP4VCNull ,
            NTP4VCTrue ,
            NTP4VCFalse
          ) ,
          NTP4VCFalse
        )
        ->
        (
          r = NTP4VCTrue
          <->
          ( NTP4VCSnapCursor A ) = NTP4VCNull
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H I $.

  $(
    Arguments are L, T, Q, O, t, stop, current stack, current snapshot,
    and the memory after marking the current node.
  $)
  ntp4vc-leaf-branch-definition $a |- (
    NTP4VCLeafBranch A B C D E F G H I
  ) <-> (
    ( NTP4VCSnapCursor H ) =/= NTP4VCNull
    /\
    A. x e. ( NTP4VCSnap A )
      (
        (
          ( NTP4VCSnapPointers x ) = ( NTP4VCMemAccessor I )
          /\
          (
            ( NTP4VCSnapCursor x )
            =
            (
              (
                ( NTP4VCMemAccessor I ) ` NTP4VCParent
              )
              ` ( NTP4VCSnapCursor H )
            )
            /\
            (
              ( NTP4VCSnapParent x ) = ( NTP4VCSnapCursor H )
              /\
              ( NTP4VCSnapMarks x ) = ( NTP4VCMemMark I )
            )
          )
        )
        ->
        (
          NTP4VCNextState
            A B C D E F H G x I
            (
              (
                ( NTP4VCMemAccessor I ) ` NTP4VCParent
              )
              ` ( NTP4VCSnapCursor H )
            )
        )
      )
  ) $.
$}

${
  $d f g h x A B C D E F G H I $.

  $(
    This is the non-leaf pointer-rotation branch. The three universally
    quantified memories reproduce the ordered Left, Right, and Parent
    updates in the source VC.
  $)
  ntp4vc-rotate-branch-definition $a |- (
    NTP4VCRotateBranch A B C D E F G H I
  ) <-> (
    ( NTP4VCSnapCursor H ) =/= NTP4VCNull
    /\
    (
      ( NTP4VCSnapCursor H ) =/= NTP4VCNull
      /\
      (
        ( NTP4VCSnapCursor H ) =/= NTP4VCNull
        /\
        A. f e. ( NTP4VCMemory A )
          (
            ( NTP4VCMemMark f ) = ( NTP4VCMemMark I )
            ->
            (
              ( NTP4VCMemAccessor f )
              =
              (
                NTP4VCUpdate
                  ( NTP4VCMemAccessor I )
                  NTP4VCLeft
                  (
                    NTP4VCUpdate
                      (
                        ( NTP4VCMemAccessor I )
                        ` NTP4VCLeft
                      )
                      ( NTP4VCSnapCursor H )
                      (
                        (
                          ( NTP4VCMemAccessor I )
                          ` NTP4VCRight
                        )
                        ` ( NTP4VCSnapCursor H )
                      )
                      A
                  )
                  NTP4VCKind
              )
              ->
              (
                ( NTP4VCSnapCursor H ) =/= NTP4VCNull
                /\
                (
                  ( NTP4VCSnapCursor H ) =/= NTP4VCNull
                  /\
                  A. g e. ( NTP4VCMemory A )
                    (
                      ( NTP4VCMemMark g ) = ( NTP4VCMemMark f )
                      ->
                      (
                        ( NTP4VCMemAccessor g )
                        =
                        (
                          NTP4VCUpdate
                            ( NTP4VCMemAccessor f )
                            NTP4VCRight
                            (
                              NTP4VCUpdate
                                (
                                  ( NTP4VCMemAccessor f )
                                  ` NTP4VCRight
                                )
                                ( NTP4VCSnapCursor H )
                                (
                                  (
                                    ( NTP4VCMemAccessor f )
                                    ` NTP4VCParent
                                  )
                                  ` ( NTP4VCSnapCursor H )
                                )
                                A
                            )
                            NTP4VCKind
                        )
                        ->
                        (
                          ( NTP4VCSnapCursor H ) =/= NTP4VCNull
                          /\
                          A. h e. ( NTP4VCMemory A )
                            (
                              ( NTP4VCMemMark h ) = ( NTP4VCMemMark g )
                              ->
                              (
                                ( NTP4VCMemAccessor h )
                                =
                                (
                                  NTP4VCUpdate
                                    ( NTP4VCMemAccessor g )
                                    NTP4VCParent
                                    (
                                      NTP4VCUpdate
                                        (
                                          ( NTP4VCMemAccessor g )
                                          ` NTP4VCParent
                                        )
                                        ( NTP4VCSnapCursor H )
                                        (
                                          (
                                            ( NTP4VCMemAccessor I )
                                            ` NTP4VCLeft
                                          )
                                          ` ( NTP4VCSnapCursor H )
                                        )
                                        A
                                    )
                                    NTP4VCKind
                                )
                                ->
                                A. x e. ( NTP4VCSnap A )
                                  (
                                    (
                                      ( NTP4VCSnapPointers x )
                                      =
                                      ( NTP4VCMemAccessor h )
                                      /\
                                      (
                                        ( NTP4VCSnapCursor x )
                                        =
                                        (
                                          (
                                            ( NTP4VCMemAccessor I )
                                            ` NTP4VCLeft
                                          )
                                          ` ( NTP4VCSnapCursor H )
                                        )
                                        /\
                                        (
                                          ( NTP4VCSnapParent x )
                                          =
                                          ( NTP4VCSnapCursor H )
                                          /\
                                          ( NTP4VCSnapMarks x )
                                          =
                                          ( NTP4VCMemMark h )
                                        )
                                      )
                                    )
                                    ->
                                    (
                                      NTP4VCNextState
                                        A B C D E F H G x h
                                        (
                                          (
                                            ( NTP4VCMemAccessor I )
                                            ` NTP4VCLeft
                                          )
                                          ` ( NTP4VCSnapCursor H )
                                        )
                                    )
                                  )
                              )
                            )
                        )
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

${
  $d b f A B C D E F G H I $.

  $(
    Arguments are L, T, Q, O, t, stop, current stack, current snapshot,
    and the memory whose mark map has just been updated.
  $)
  ntp4vc-non-null-branch-definition $a |- (
    NTP4VCNonNullBranch A B C D E F G H I
  ) <-> (
    ( NTP4VCSnapCursor H ) =/= NTP4VCNull
    /\
    A. f e. ( NTP4VCMemory A )
      (
        ( NTP4VCMemAccessor f ) = ( NTP4VCMemAccessor I )
        ->
        (
          ( NTP4VCMemMark f )
          =
          (
            NTP4VCUpdate
              ( NTP4VCMemMark I )
              ( NTP4VCSnapCursor H )
              NTP4VCTrue A
          )
          ->
          (
            ( NTP4VCSnapCursor H ) =/= NTP4VCNull
            /\
            (
              (
                (
                  ( NTP4VCMemAccessor f ) ` NTP4VCLeft
                )
                ` ( NTP4VCSnapCursor H )
              )
              =
              NTP4VCNull
              ->
              ( NTP4VCSnapCursor H ) =/= NTP4VCNull
            )
            /\
            A. b e. NTP4VCBool
              (
                b
                =
                if (
                  (
                    (
                      ( NTP4VCMemAccessor f ) ` NTP4VCLeft
                    )
                    ` ( NTP4VCSnapCursor H )
                  )
                  =
                  NTP4VCNull ,
                  if (
                    (
                      (
                        ( NTP4VCMemAccessor f ) ` NTP4VCRight
                      )
                      ` ( NTP4VCSnapCursor H )
                    )
                    =
                    NTP4VCNull ,
                    NTP4VCTrue ,
                    NTP4VCFalse
                  ) ,
                  NTP4VCFalse
                )
                ->
                (
                  (
                    b = NTP4VCTrue
                    ->
                    (
                      NTP4VCLeafBranch
                        A B C D E F G H f
                    )
                  )
                  /\
                  (
                    b =/= NTP4VCTrue
                    ->
                    (
                      NTP4VCRotateBranch
                        A B C D E F G H f
                    )
                  )
                )
              )
          )
        )
      )
  ) $.
$}

ntp4vc-terminal-branch-definition $a |- (
  NTP4VCTerminalBranch A B C D E F G H
) <-> (
  F = NTP4VCDone
  /\
  (
    F = NTP4VCDone
    ->
    (
      (
        (
          NTP4VCExt
            A
            ( NTP4VCFootprint C )
            ( NTP4VCSnapPointers E )
            ( NTP4VCMemAccessor H )
        )
        /\
        (
          NTP4VCIsTree
            ( NTP4VCSnapPointers E )
            C D NTP4VCNull
        )
      )
      /\
      (
        (
          NTP4VCIsTree
            ( NTP4VCMemAccessor H )
            C D NTP4VCNull
        )
        ->
        (
          (
            NTP4VCIsTree
              ( NTP4VCMemAccessor H )
              C D NTP4VCNull
          )
          /\
          (
            NTP4VCUnchanged
              A
              ( NTP4VCMemAccessor B )
              ( NTP4VCMemAccessor H )
            /\
            (
              NTP4VCWasMarked
                A C
                ( NTP4VCMemMark B )
                ( NTP4VCMemMark H )
            )
          )
        )
      )
    )
  )
) $.

${
  $d A B C D E F G H I J K L $.

  $(
    Arguments are L, T, Q, O, initial memory, t, root, stop, current stack,
    current snapshot, current memory, and the entered flag.
  $)
  ntp4vc-iteration-definition $a |- (
    NTP4VCIteration A B C D E F G H I J K L
  ) <-> (
    (
      (
        ( NTP4VCSnapCursor J ) = NTP4VCNull
        ->
        L = NTP4VCTrue
      )
      /\
      (
        ( NTP4VCSnapPointers J ) = ( NTP4VCMemAccessor K )
        /\
        (
          ( NTP4VCSnapMarks J ) = ( NTP4VCMemMark K )
          /\
          ( NTP4VCIsStack A F H J I NTP4VCNone )
        )
      )
    )
    ->
    (
      ( NTP4VCResultCheck J L )
      /\
      (
        (
          ( NTP4VCSnapCursor J ) =/= NTP4VCNull
          ->
          (
            NTP4VCNonNullBranch
              A B C D F H I J K
          )
        )
        /\
        (
          ( NTP4VCSnapCursor J ) = NTP4VCNull
          ->
          (
            NTP4VCTerminalBranch
              A E F G H I J K
          )
        )
      )
    )
  ) $.
$}

${
  $d e m q s A B C D E F G H I $.

  $(
    Arguments are L, T, Q, O, initial memory, t, root, stop, and the
    arbitrary outer-loop stack.
  $)
  ntp4vc-outer-state-definition $a |- (
    NTP4VCOuterState A B C D E F G H I
  ) <-> (
    (
      G =/= NTP4VCNull
      /\
      (
        ( NTP4VCSnapPointers H ) = ( NTP4VCMemAccessor E )
        /\
        (
          ( NTP4VCSnapCursor H ) = G
          /\
          (
            ( NTP4VCSnapParent H ) = NTP4VCNull
            /\
            (
              ( NTP4VCSnapMarks H ) = ( NTP4VCMemMark E )
              /\
              ( NTP4VCIsStack A F H H I NTP4VCNone )
            )
          )
        )
      )
    )
    /\
    A. e e. NTP4VCBool
      A. q e. C
        A. s e. ( NTP4VCSnap A )
          A. m e. ( NTP4VCMemory A )
            (
              NTP4VCIteration
                A B C D E F G H q s m e
            )
  ) $.
$}

${
  $d q s A B C D E F G $.

  ntp4vc-mark-tree-vc-definition $a |- (
    NTP4VCMarkTreeVC A B C D E F G
  ) <-> (
    A. s e. ( NTP4VCSnap A )
      (
        (
          ( NTP4VCSnapPointers s ) = ( NTP4VCMemAccessor E )
          /\
          (
            ( NTP4VCSnapCursor s ) = G
            /\
            (
              ( NTP4VCSnapParent s ) = NTP4VCNull
              /\
              ( NTP4VCSnapMarks s ) = ( NTP4VCMemMark E )
            )
          )
        )
        ->
        (
          (
            ( NTP4VCIsStack A F s s NTP4VCBottom ( NTP4VCSome F ) )
            /\
            (
              (
                NTP4VCIsTree
                  ( NTP4VCSnapPointers s )
                  F
                  ( NTP4VCSnapCursor s )
                  ( NTP4VCSnapParent s )
              )
              /\
              ( NTP4VCSnapCursor s ) =/= NTP4VCNull
            )
          )
          /\
          A. q e. C
            (
              (
                ( NTP4VCIsStack A F s s q NTP4VCNone )
                /\
                (
                  ( NTP4VCStackSize q )
                  <_
                  (
                    ( NTP4VCStackSize NTP4VCBottom )
                    +
                    ( ; ; 1 0 0 x. ( NTP4VCSize F ) )
                  )
                )
              )
              ->
              (
                NTP4VCOuterState
                  A B C D E F G s q
              )
            )
        )
      )
  ) $.
$}

${
  $d a b c d e f g h i j k l m n o p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary location carrier and distinguished null value. $)
  ntp4vc-location-carrier-nonempty $e |- L =/= (/) $.
  ntp4vc-null-location $e |- NTP4VCNull e. L $.

  $( Exact finite location-labelled binary-tree datatype. $)
  ntp4vc-tree-empty-closure $e |- NTP4VCEmpty e. T $.

  ntp4vc-tree-node-closure $e |- A. l e. T A. x e. L A. r e. T
    ( NTP4VCNode l x r ) e. T $.

  ntp4vc-tree-constructor-exhaustive $e |- A. t e. T
    (
      t = NTP4VCEmpty
      \/
      E. l e. T E. x e. L E. r e. T
        t = ( NTP4VCNode l x r )
    ) $.

  ntp4vc-tree-structural-induction $e |- A. s e. ~P T
    (
      (
        NTP4VCEmpty e. s
        /\
        A. l e. T A. x e. L A. r e. T
          (
            (
              l e. s
              /\
              r e. s
            )
            ->
            ( NTP4VCNode l x r ) e. s
          )
      )
      ->
      s = T
    ) $.

  $( Exact option datatype over trees. $)
  ntp4vc-option-none-closure $e |- NTP4VCNone e. O $.

  ntp4vc-option-some-closure $e |- A. t e. T
    ( NTP4VCSome t ) e. O $.

  ntp4vc-option-constructor-exhaustive $e |- A. o e. O
    (
      o = NTP4VCNone
      \/
      E. t e. T o = ( NTP4VCSome t )
    ) $.

  $( Exact finite simulated-call-stack datatype. $)
  ntp4vc-stack-bottom-closure $e |- NTP4VCBottom e. Q $.
  ntp4vc-stack-done-closure $e |- NTP4VCDone e. Q $.

  ntp4vc-stack-running-closure $e |- A. s e. Q A. p e. ZZ
    A. f e. ( NTP4VCFrame L T )
      ( NTP4VCRunning s p f ) e. Q $.

  ntp4vc-stack-constructor-exhaustive $e |- A. q e. Q
    (
      q = NTP4VCBottom
      \/
      (
        q = NTP4VCDone
        \/
        E. s e. Q E. p e. ZZ E. f e. ( NTP4VCFrame L T )
          q = ( NTP4VCRunning s p f )
      )
    ) $.

  ntp4vc-stack-structural-induction $e |- A. a e. ~P Q
    (
      (
        (
          NTP4VCBottom e. a
          /\
          NTP4VCDone e. a
        )
        /\
        A. s e. Q A. p e. ZZ A. f e. ( NTP4VCFrame L T )
          (
            s e. a
            ->
            ( NTP4VCRunning s p f ) e. a
          )
      )
      ->
      a = Q
    ) $.

  $( Complete recursive footprint and integer tree-size definitions. $)
  ntp4vc-footprint-typing $e |- A. t e. T
    ( NTP4VCFootprint t ) C_ L $.

  ntp4vc-footprint-empty $e |- (
    NTP4VCFootprint NTP4VCEmpty
  ) = (/) $.

  ntp4vc-footprint-node $e |- A. l e. T A. x e. L A. r e. T
    (
      NTP4VCFootprint ( NTP4VCNode l x r )
    )
    =
    (
      { x }
      u.
      (
        ( NTP4VCFootprint l )
        u.
        ( NTP4VCFootprint r )
      )
    ) $.

  ntp4vc-size-typing $e |- A. t e. T
    ( NTP4VCSize t ) e. ZZ $.

  ntp4vc-size-empty $e |- (
    NTP4VCSize NTP4VCEmpty
  ) = 0 $.

  ntp4vc-size-node $e |- A. l e. T A. x e. L A. r e. T
    (
      NTP4VCSize ( NTP4VCNode l x r )
    )
    =
    (
      1
      +
      (
        ( NTP4VCSize l )
        +
        ( NTP4VCSize r )
      )
    ) $.

  $( Complete recursive definition of the source is_tree predicate. $)
  ntp4vc-is-tree-empty $e |- A. a e. ( NTP4VCAccessors L )
    A. c e. L A. p e. L
      (
        NTP4VCIsTree a NTP4VCEmpty c p
      ) <-> (
        c = NTP4VCNull
      ) $.

  ntp4vc-is-tree-node $e |- A. a e. ( NTP4VCAccessors L )
    A. l e. T A. m e. L A. r e. T A. c e. L A. p e. L
      (
        NTP4VCIsTree a ( NTP4VCNode l m r ) c p
      ) <-> (
        c =/= NTP4VCNull
        /\
        (
          c = m
          /\
          (
            ( ( a ` NTP4VCParent ) ` c ) = p
            /\
            (
              (
                ( ( a ` NTP4VCLeft ) ` c ) = NTP4VCNull
                <->
                ( ( a ` NTP4VCRight ) ` c ) = NTP4VCNull
              )
              /\
              (
                (
                  NTP4VCIsTree
                    a l
                    ( ( a ` NTP4VCLeft ) ` c )
                    c
                )
                /\
                (
                  NTP4VCIsTree
                    a r
                    ( ( a ` NTP4VCRight ) ` c )
                    c
                )
              )
            )
          )
        )
      ) $.

  $( Complete recursive definition of the simulated-stack predicate. $)
  ntp4vc-is-stack-bottom $e |- A. t e. T
    A. d e. ( NTP4VCSnap L ) A. c e. ( NTP4VCSnap L )
      A. o e. O
        (
          NTP4VCIsStack L t d c NTP4VCBottom o
        ) <-> (
          d = c
          /\
          o = ( NTP4VCSome t )
        ) $.

  ntp4vc-is-stack-done $e |- A. t e. T
    A. d e. ( NTP4VCSnap L ) A. c e. ( NTP4VCSnap L )
      A. o e. O
        (
          NTP4VCIsStack L t d c NTP4VCDone o
        ) <-> (
          ( NTP4VCRecRel L t d c )
          /\
          o = NTP4VCNone
        ) $.

  ntp4vc-is-stack-running $e |- A. t e. T
    A. d e. ( NTP4VCSnap L ) A. c e. ( NTP4VCSnap L )
      A. s e. Q A. p e. ZZ A. f e. ( NTP4VCFrame L T )
        A. o e. O
          (
            NTP4VCIsStack L t d c ( NTP4VCRunning s p f ) o
          ) <-> (
            (
              0 <_ p
              /\
              p <_ 4
            )
            /\
            (
              NTP4VCIsStack
                L t d
                ( NTP4VCMemo0 f )
                s
                ( NTP4VCSome ( NTP4VCTreeField f ) )
            )
            /\
            (
              ( NTP4VCSnapCursor ( NTP4VCMemo0 f ) )
              =/=
              NTP4VCNull
            )
            /\
            (
              NTP4VCIsTree
                ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
                ( NTP4VCTreeField f )
                ( NTP4VCSnapCursor ( NTP4VCMemo0 f ) )
                ( NTP4VCSnapParent ( NTP4VCMemo0 f ) )
            )
            /\
            (
              ( NTP4VCTreeField f )
              =
              (
                NTP4VCNode
                  ( NTP4VCTLeft f )
                  ( NTP4VCSnapCursor ( NTP4VCMemo0 f ) )
                  ( NTP4VCTRight f )
              )
            )
            /\
            (
              ( NTP4VCPLeft f )
              =
              (
                (
                  ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
                  ` NTP4VCLeft
                )
                ` ( NTP4VCSnapCursor ( NTP4VCMemo0 f ) )
              )
            )
            /\
            (
              ( NTP4VCPRight f )
              =
              (
                (
                  ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
                  ` NTP4VCRight
                )
                ` ( NTP4VCSnapCursor ( NTP4VCMemo0 f ) )
              )
            )
            /\
            (
              1 <_ p
              ->
              (
                (
                  NTP4VCBlocRel
                    L NTP4VCGoLeft
                    ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
                    ( NTP4VCMemo0 f )
                    ( NTP4VCMemo1 f )
                )
                /\
                (
                  ( NTP4VCPLeft f ) =/= NTP4VCNull
                  /\
                  ( NTP4VCPRight f ) =/= NTP4VCNull
                )
              )
            )
            /\
            (
              2 <_ p
              ->
              (
                NTP4VCRecRel
                  L
                  ( NTP4VCTLeft f )
                  ( NTP4VCMemo1 f )
                  ( NTP4VCMemo2 f )
              )
            )
            /\
            (
              3 <_ p
              ->
              (
                NTP4VCBlocRel
                  L NTP4VCGoRight
                  ( NTP4VCSnapPointers ( NTP4VCMemo0 f ) )
                  ( NTP4VCMemo2 f )
                  ( NTP4VCMemo3 f )
              )
            )
            /\
            (
              4 <_ p
              ->
              (
                NTP4VCRecRel
                  L
                  ( NTP4VCTRight f )
                  ( NTP4VCMemo3 f )
                  ( NTP4VCMemo4 f )
              )
            )
            /\
            (
              ( NTP4VCFrameMemo f p ) = c
              /\
              (
                (
                  o = NTP4VCNone
                  ->
                  (
                    p =/= 1
                    /\
                    p =/= 3
                  )
                )
                /\
                A. u e. T
                  (
                    o = ( NTP4VCSome u )
                    ->
                    (
                      (
                        p = 1
                        ->
                        u = ( NTP4VCTLeft f )
                      )
                      /\
                      (
                        p =/= 1
                        ->
                        (
                          p = 3
                          /\
                          u = ( NTP4VCTRight f )
                        )
                      )
                    )
                  )
              )
            )
          ) $.

  $( Complete recursive integer stack-size definition. $)
  ntp4vc-stack-size-typing $e |- A. q e. Q
    ( NTP4VCStackSize q ) e. ZZ $.

  ntp4vc-stack-size-bottom $e |- (
    NTP4VCStackSize NTP4VCBottom
  ) = 1 $.

  ntp4vc-stack-size-done $e |- (
    NTP4VCStackSize NTP4VCDone
  ) = 0 $.

  ntp4vc-stack-size-running $e |- A. s e. Q A. p e. ZZ
    A. f e. ( NTP4VCFrame L T )
      (
        NTP4VCStackSize ( NTP4VCRunning s p f )
      )
      =
      (
        (
          ( NTP4VCStackSize s )
          +
          ( ; ; 1 0 0 - p )
        )
        +
        if (
          p = 0 ,
          (
            ; ; 1 0 0
            x.
            (
              ( NTP4VCSize ( NTP4VCTLeft f ) )
              +
              ( NTP4VCSize ( NTP4VCTRight f ) )
            )
          ) ,
          if (
            p <_ 2 ,
            (
              ; ; 1 0 0
              x.
              ( NTP4VCSize ( NTP4VCTRight f ) )
            ) ,
            0
          )
        )
      ) $.

  $( Source theorem parameters and its two assumptions. $)
  ntp4vc-memory-parameter $e |- M e. ( NTP4VCMemory L ) $.
  ntp4vc-tree-parameter $e |- R e. T $.
  ntp4vc-root-parameter $e |- P e. L $.

  ntp4vc-fact0 $e |- (
    NTP4VCIsTree
      ( NTP4VCMemAccessor M )
      R P NTP4VCNull
  ) $.

  ntp4vc-fact1 $e |- P =/= NTP4VCNull $.

  ntp4vc-pearl-verifythis-2016-tree-traversal-iterative-mark-tree-vc
    $a |- (
      NTP4VCMarkTreeVC L T Q O M R P
    ) $.
$}
