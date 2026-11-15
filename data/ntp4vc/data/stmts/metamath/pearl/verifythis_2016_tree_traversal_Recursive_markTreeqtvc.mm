$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc
  (ntp4vc__metamath__pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc):
  the recursive Morris-style binary-tree traversal verification condition
  preserves the pointer structure while marking both recursive subtrees and
  restoring the original tree shape. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  L is an arbitrary nonempty location carrier with distinguished null
  location. Booleans, pointer kinds, and traversal phases are represented by
  exact finite carriers. A memory is the full Cartesian product of the source
  total accessor and mark function spaces, so every source memory value and
  every quantified intermediate update remains available.

  T is exactly the finite inductive carrier of location-labelled binary trees.
  Its tagged constructors, closure and exhaustiveness laws, and structural
  induction principle exclude both missing finite trees and extraneous
  non-well-founded values. The scoped equations are the complete recursive
  definitions of footprint and is_tree. Every remaining predicate is a
  literal set-theoretic expansion of the original Why3 verification
  condition. Proposition-valued conditionals and datatype matches are split
  into equivalent guarded branches over exhaustive carriers. Repeated
  non-null obligations, all universal memory quantifiers, and the ordered
  nested Left, Right, and Parent updates are retained.

  The final $a is Metamath's native unproved statement encoding. Every
  preceding $a is syntax or a faithful definition; this database contains no
  proof declaration.
$)

$c
  NTP4VCBool NTP4VCFalse NTP4VCTrue
  NTP4VCKind NTP4VCParent NTP4VCLeft NTP4VCRight
  NTP4VCPhase NTP4VCGoLeft NTP4VCGoRight NTP4VCGoBack NTP4VCFinish
  NTP4VCNull
  NTP4VCAccessors NTP4VCMarks NTP4VCMemory
  NTP4VCMemAccessor NTP4VCMemMark
  NTP4VCEmpty NTP4VCNode NTP4VCUpdate NTP4VCFootprint
  NTP4VCIsTree NTP4VCExt NTP4VCUnchanged NTP4VCWasMarked
  NTP4VCNextPhase NTP4VCRotated
  NTP4VCOldLeaf NTP4VCBlocPost NTP4VCFinalUpdate
  NTP4VCRotateUpdates NTP4VCBlocObligation
  NTP4VCSubtrees NTP4VCChildOf NTP4VCResultCheck NTP4VCFinalPost
  NTP4VCAfterMemo4 NTP4VCAfterMemo3 NTP4VCNonleaf
  NTP4VCAfterMemo2 NTP4VCRecursivePair NTP4VCRecursiveCalls
  NTP4VCFinishLocation NTP4VCFinishMemories NTP4VCTopFinish
  NTP4VCMarkTreeVC
$.

ntp4vc-bool-syntax $a class NTP4VCBool $.
ntp4vc-false-syntax $a class NTP4VCFalse $.
ntp4vc-true-syntax $a class NTP4VCTrue $.
ntp4vc-kind-syntax $a class NTP4VCKind $.
ntp4vc-parent-syntax $a class NTP4VCParent $.
ntp4vc-left-syntax $a class NTP4VCLeft $.
ntp4vc-right-syntax $a class NTP4VCRight $.
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
ntp4vc-empty-syntax $a class NTP4VCEmpty $.
ntp4vc-node-syntax $a class ( NTP4VCNode A B C ) $.
ntp4vc-update-syntax $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-footprint-syntax $a class ( NTP4VCFootprint A ) $.

ntp4vc-is-tree-syntax
  $a wff ( NTP4VCIsTree A B C D ) $.
ntp4vc-ext-syntax
  $a wff ( NTP4VCExt A B C D ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C ) $.
ntp4vc-was-marked-syntax
  $a wff ( NTP4VCWasMarked A B C D ) $.
ntp4vc-next-phase-syntax
  $a class ( NTP4VCNextPhase A ) $.
ntp4vc-rotated-syntax
  $a wff ( NTP4VCRotated A B C D E ) $.
ntp4vc-old-leaf-syntax
  $a wff ( NTP4VCOldLeaf A B ) $.
ntp4vc-bloc-post-syntax
  $a wff ( NTP4VCBlocPost A B C D E F ) $.
ntp4vc-final-update-syntax
  $a wff ( NTP4VCFinalUpdate A B C D E F G ) $.
ntp4vc-rotate-updates-syntax
  $a wff ( NTP4VCRotateUpdates A B C D E F ) $.
ntp4vc-bloc-obligation-syntax
  $a wff ( NTP4VCBlocObligation A ) $.
ntp4vc-subtrees-syntax
  $a wff ( NTP4VCSubtrees A B C D E ) $.
ntp4vc-child-of-syntax
  $a wff ( NTP4VCChildOf A B C D ) $.
ntp4vc-result-check-syntax
  $a wff ( NTP4VCResultCheck A B C D ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C D E F ) $.
ntp4vc-after-memo4-syntax
  $a wff ( NTP4VCAfterMemo4 A B C D E F G H I J ) $.
ntp4vc-after-memo3-syntax
  $a wff ( NTP4VCAfterMemo3 A B C D E F G H I J ) $.
ntp4vc-nonleaf-syntax
  $a wff ( NTP4VCNonleaf A B C D E F G H I J K L M ) $.
ntp4vc-after-memo2-syntax
  $a wff ( NTP4VCAfterMemo2 A B C D E F G H I J K L M ) $.
ntp4vc-recursive-pair-syntax
  $a wff ( NTP4VCRecursivePair A B C D E F G H I J K ) $.
ntp4vc-recursive-calls-syntax
  $a wff ( NTP4VCRecursiveCalls A B ) $.
ntp4vc-finish-location-syntax
  $a wff ( NTP4VCFinishLocation A B C D E F G H ) $.
ntp4vc-finish-memories-syntax
  $a wff ( NTP4VCFinishMemories A B C D E F ) $.
ntp4vc-top-finish-syntax
  $a wff ( NTP4VCTopFinish A B C D E ) $.
ntp4vc-mark-tree-vc-syntax
  $a wff ( NTP4VCMarkTreeVC A B C D E ) $.

ntp4vc-bool-definition $a |- NTP4VCBool = ( 0 ..^ 2 ) $.
ntp4vc-false-definition $a |- NTP4VCFalse = 0 $.
ntp4vc-true-definition $a |- NTP4VCTrue = 1 $.
ntp4vc-kind-definition $a |- NTP4VCKind = ( 0 ..^ 3 ) $.
ntp4vc-parent-definition $a |- NTP4VCParent = 0 $.
ntp4vc-left-definition $a |- NTP4VCLeft = 1 $.
ntp4vc-right-definition $a |- NTP4VCRight = 2 $.
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

ntp4vc-empty-definition $a |- NTP4VCEmpty = <. 0 , (/) >. $.

ntp4vc-node-definition $a |- (
  NTP4VCNode A B C
) = <. 1 , <. A , <. B , C >. >. >. $.

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

ntp4vc-old-leaf-definition $a |- (
  NTP4VCOldLeaf A B
) <-> (
  (
    ( ( ( NTP4VCMemAccessor A ) ` NTP4VCLeft ) ` B )
    =
    NTP4VCNull
  )
  /\
  (
    NTP4VCNull
    =
    ( ( ( NTP4VCMemAccessor A ) ` NTP4VCRight ) ` B )
  )
) $.

${
  $d x A B C D E F $.
  ntp4vc-bloc-post-definition $a |- (
    NTP4VCBlocPost A B C D E F
  ) <-> (
    (
      ( ( NTP4VCMemMark C ) ` F ) = NTP4VCTrue
      /\
      A. x e. A
        (
          x =/= F
          ->
          ( ( NTP4VCMemMark C ) ` x )
          =
          ( ( NTP4VCMemMark B ) ` x )
        )
    )
    /\
    (
      (
        ( NTP4VCOldLeaf B F )
        ->
        ( NTP4VCMemAccessor C ) = ( NTP4VCMemAccessor B )
      )
      /\
      (
        -. ( NTP4VCOldLeaf B F )
        ->
        (
          NTP4VCRotated
            A D ( NTP4VCMemAccessor C )
            ( NTP4VCNextPhase E ) F
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G $.
  ntp4vc-final-update-definition $a |- (
    NTP4VCFinalUpdate A B C D E F G
  ) <-> (
    (
      ( ( ( NTP4VCMemAccessor F ) ` NTP4VCLeft ) ` B )
      =
      ( ( ( NTP4VCMemAccessor G ) ` NTP4VCParent ) ` B )
    )
    /\
    E =/= NTP4VCFinish
    /\
    (
      ( ( NTP4VCMemMark G ) ` B ) = NTP4VCTrue
      /\
      A. x e. A
        (
          x =/= B
          ->
          ( ( NTP4VCMemMark G ) ` x )
          =
          ( ( NTP4VCMemMark C ) ` x )
        )
    )
    /\
    (
      (
        ( NTP4VCOldLeaf C B )
        ->
        ( NTP4VCMemAccessor G ) = ( NTP4VCMemAccessor C )
      )
      /\
      (
        -. ( NTP4VCOldLeaf C B )
        ->
        (
          NTP4VCRotated
            A D ( NTP4VCMemAccessor G )
            ( NTP4VCNextPhase E ) B
        )
      )
    )
  ) $.
$}

${
  $d f g h A B C D E F $.
  ntp4vc-rotate-updates-definition $a |- (
    NTP4VCRotateUpdates A B C D E F
  ) <-> (
    B =/= NTP4VCNull
    /\
    (
      B =/= NTP4VCNull
      /\
      (
        B =/= NTP4VCNull
        /\
        A. f e. ( NTP4VCMemory A )
          (
            ( NTP4VCMemMark f ) = ( NTP4VCMemMark F )
            ->
            (
              ( NTP4VCMemAccessor f )
              =
              (
                NTP4VCUpdate
                  ( NTP4VCMemAccessor F )
                  NTP4VCLeft
                  (
                    NTP4VCUpdate
                      ( ( NTP4VCMemAccessor F ) ` NTP4VCLeft )
                      B
                      (
                        ( ( NTP4VCMemAccessor F ) ` NTP4VCRight )
                        ` B
                      )
                      A
                  )
                  NTP4VCKind
              )
              ->
              (
                B =/= NTP4VCNull
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
                              B
                              (
                                (
                                  ( NTP4VCMemAccessor f )
                                  ` NTP4VCParent
                                )
                                ` B
                              )
                              A
                          )
                          NTP4VCKind
                      )
                      ->
                      (
                        B =/= NTP4VCNull
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
                                      B
                                      (
                                        (
                                          ( NTP4VCMemAccessor F )
                                          ` NTP4VCLeft
                                        )
                                        ` B
                                      )
                                      A
                                  )
                                  NTP4VCKind
                              )
                              ->
                              (
                                NTP4VCFinalUpdate
                                  A B C D E F h
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
  $d b e f g h i j x A $.
  ntp4vc-bloc-obligation-definition $a |- (
    NTP4VCBlocObligation A
  ) <-> (
    A. e e. NTP4VCBool
      A. x e. A
        A. f e. ( NTP4VCMemory A )
          A. g e. ( NTP4VCAccessors A )
            A. h e. NTP4VCPhase
              (
                (
                  (
                    NTP4VCRotated
                      A g ( NTP4VCMemAccessor f ) h x
                  )
                  /\
                  (
                    h = NTP4VCFinish
                    ->
                    e = NTP4VCTrue
                  )
                )
                ->
                A. b e. NTP4VCBool
                  (
                    b
                    =
                    if (
                      e = NTP4VCTrue ,
                      if (
                        x = NTP4VCNull ,
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
                        h = NTP4VCFinish
                      )
                      /\
                      (
                        b =/= NTP4VCTrue
                        ->
                        (
                          x =/= NTP4VCNull
                          /\
                          A. i e. ( NTP4VCMemory A )
                            (
                              ( NTP4VCMemAccessor i )
                              =
                              ( NTP4VCMemAccessor f )
                              ->
                              (
                                ( NTP4VCMemMark i )
                                =
                                (
                                  NTP4VCUpdate
                                    ( NTP4VCMemMark f )
                                    x NTP4VCTrue A
                                )
                                ->
                                (
                                  x =/= NTP4VCNull
                                  /\
                                  (
                                    (
                                      (
                                        (
                                          ( NTP4VCMemAccessor i )
                                          ` NTP4VCLeft
                                        )
                                        ` x
                                      )
                                      =
                                      NTP4VCNull
                                      ->
                                      x =/= NTP4VCNull
                                    )
                                    /\
                                    A. j e. NTP4VCBool
                                      (
                                        j
                                        =
                                        if (
                                          (
                                            (
                                              (
                                                NTP4VCMemAccessor i
                                              )
                                              ` NTP4VCLeft
                                            )
                                            ` x
                                          )
                                          =
                                          NTP4VCNull ,
                                          if (
                                            (
                                              (
                                                (
                                                  NTP4VCMemAccessor i
                                                )
                                                ` NTP4VCRight
                                              )
                                              ` x
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
                                            j = NTP4VCTrue
                                            ->
                                            (
                                              x =/= NTP4VCNull
                                              /\
                                              (
                                                h =/= NTP4VCFinish
                                                /\
                                                (
                                                  NTP4VCBlocPost
                                                    A f i g h x
                                                )
                                              )
                                            )
                                          )
                                          /\
                                          (
                                            j =/= NTP4VCTrue
                                            ->
                                            (
                                              NTP4VCRotateUpdates
                                                A x f g h i
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
  $d m A B C D E $.
  ntp4vc-subtrees-definition $a |- (
    NTP4VCSubtrees A B C D E
  ) <-> (
    E. m e. A C = ( NTP4VCNode D m E )
  ) $.
$}

${
  $d l m r A B C D $.
  ntp4vc-child-of-definition $a |- (
    NTP4VCChildOf A B C D
  ) <-> (
    E. l e. B E. m e. A E. r e. B
      (
        C = ( NTP4VCNode l m r )
        /\
        (
          l = D
          \/
          r = D
        )
      )
  ) $.
$}

${
  $d r A B C D $.
  ntp4vc-result-check-definition $a |- (
    NTP4VCResultCheck A B C D
  ) <-> (
    A. r e. NTP4VCBool
      (
        r
        =
        if (
          A = NTP4VCNull ,
          if (
            B = NTP4VCNull ,
            NTP4VCTrue ,
            NTP4VCFalse
          ) ,
          NTP4VCFalse
        )
        ->
        (
          (
            r = NTP4VCTrue
            <->
            (
              A = NTP4VCNull
              /\
              B = NTP4VCNull
            )
          )
          /\
          (
            r = NTP4VCTrue
            ->
            (
              C = NTP4VCEmpty
              /\
              D = NTP4VCEmpty
            )
          )
        )
      )
  ) $.
$}

ntp4vc-final-post-definition $a |- (
  NTP4VCFinalPost A B C D E F
) <-> (
  (
    NTP4VCUnchanged
      A
      ( NTP4VCMemAccessor B )
      ( NTP4VCMemAccessor C )
  )
  /\
  (
    (
      ( ( NTP4VCMemAccessor C ) ` NTP4VCParent )
      ` E
    )
    =
    F
  )
  /\
  (
    NTP4VCWasMarked
      A D
      ( NTP4VCMemMark B )
      ( NTP4VCMemMark C )
  )
) $.

${
  $d f g A B C D E F G H I J $.
  ntp4vc-after-memo4-definition $a |- (
    NTP4VCAfterMemo4 A B C D E F G H I J
  ) <-> (
    (
      (
        NTP4VCExt
          A ( NTP4VCFootprint E ) G
          ( NTP4VCMemAccessor J )
      )
      /\
      (
        NTP4VCIsTree G E F H
      )
    )
    /\
    (
      (
        NTP4VCIsTree
          ( NTP4VCMemAccessor J ) E F H
      )
      ->
      (
        (
          (
            NTP4VCChildOf A B D E
          )
          /\
          (
            (
              (
                ( NTP4VCMemAccessor J ) ` NTP4VCParent
              )
              ` H
            )
            =/=
            NTP4VCNull
          )
          /\
          (
            NTP4VCIsTree
              ( NTP4VCMemAccessor J ) E
              (
                (
                  ( NTP4VCMemAccessor J ) ` NTP4VCParent
                )
                ` H
              )
              H
          )
        )
        /\
        A. f e. ( NTP4VCMemory A )
          (
            (
              (
                NTP4VCUnchanged
                  A
                  ( NTP4VCMemAccessor J )
                  ( NTP4VCMemAccessor f )
              )
              /\
              (
                NTP4VCWasMarked
                  A E
                  ( NTP4VCMemMark J )
                  ( NTP4VCMemMark f )
              )
            )
            ->
            (
              (
                NTP4VCRotated
                  A G ( NTP4VCMemAccessor f )
                  NTP4VCGoBack H
              )
              /\
              A. g e. ( NTP4VCMemory A )
                (
                  (
                    NTP4VCBlocPost
                      A f g G NTP4VCGoBack H
                  )
                  ->
                  (
                    NTP4VCFinalPost A C g D H I
                  )
                )
            )
          )
      )
    )
  ) $.
$}

${
  $d f A B C D E F G H I J $.
  ntp4vc-after-memo3-definition $a |- (
    NTP4VCAfterMemo3 A B C D E F G H I J
  ) <-> (
    (
      NTP4VCRotated
        A G ( NTP4VCMemAccessor J )
        NTP4VCGoRight H
    )
    /\
    A. f e. ( NTP4VCMemory A )
      (
        (
          NTP4VCBlocPost
            A J f G NTP4VCGoRight H
        )
        ->
        (
          NTP4VCAfterMemo4
            A B C D E F G H I f
        )
      )
  ) $.
$}

${
  $d f A B C D E F G H I J K L M $.
  ntp4vc-nonleaf-definition $a |- (
    NTP4VCNonleaf A B C D E F G H I J K L M
  ) <-> (
    (
      (
        NTP4VCExt
          A ( NTP4VCFootprint E ) I
          ( NTP4VCMemAccessor M )
      )
      /\
      (
        NTP4VCIsTree I E G J
      )
    )
    /\
    (
      (
        NTP4VCIsTree
          ( NTP4VCMemAccessor M ) E G J
      )
      ->
      (
        (
          (
            NTP4VCChildOf A B D E
          )
          /\
          (
            (
              (
                ( NTP4VCMemAccessor M ) ` NTP4VCParent
              )
              ` J
            )
            =/=
            NTP4VCNull
          )
          /\
          (
            NTP4VCIsTree
              ( NTP4VCMemAccessor M ) E
              (
                (
                  ( NTP4VCMemAccessor M ) ` NTP4VCParent
                )
                ` J
              )
              J
          )
        )
        /\
        A. f e. ( NTP4VCMemory A )
          (
            (
              (
                NTP4VCUnchanged
                  A
                  ( NTP4VCMemAccessor M )
                  ( NTP4VCMemAccessor f )
              )
              /\
              (
                NTP4VCWasMarked
                  A E
                  ( NTP4VCMemMark M )
                  ( NTP4VCMemMark f )
              )
            )
            ->
            (
              NTP4VCAfterMemo3
                A B C D F H I J L f
            )
          )
      )
    )
  ) $.
$}

ntp4vc-after-memo2-definition $a |- (
  NTP4VCAfterMemo2 A B C D E F G H I J K L M
) <-> (
  (
    NTP4VCResultCheck G H E F
  )
  /\
  (
    (
      (
        (
          G = NTP4VCNull
          /\
          H = NTP4VCNull
        )
        ->
        (
          E = NTP4VCEmpty
          /\
          F = NTP4VCEmpty
        )
      )
      ->
      (
        (
          -.
          (
            G = NTP4VCNull
            /\
            H = NTP4VCNull
          )
          ->
          (
            NTP4VCNonleaf
              A B C D E F G H I J K L M
          )
        )
        /\
        (
          (
            G = NTP4VCNull
            /\
            H = NTP4VCNull
          )
          ->
          (
            NTP4VCFinalPost A C M D J L
          )
        )
      )
    )
  )
) $.

${
  $d f A B C D E F G H I J K $.
  ntp4vc-recursive-pair-definition $a |- (
    NTP4VCRecursivePair A B C D E F G H I J K
  ) <-> (
    (
      NTP4VCIsTree
        I ( NTP4VCNode E J F ) J K
    )
    /\
    (
      (
        -. J e. ( NTP4VCFootprint E )
        /\
        -. J e. ( NTP4VCFootprint F )
      )
      ->
      (
        (
          NTP4VCRotated
            A I ( NTP4VCMemAccessor C )
            NTP4VCGoLeft J
        )
        /\
        A. f e. ( NTP4VCMemory A )
          (
            (
              NTP4VCBlocPost
                A C f I NTP4VCGoLeft J
            )
            ->
            (
              NTP4VCAfterMemo2
                A B C D E F G H I J K K f
            )
          )
      )
    )
  ) $.
$}

${
  $d f g h i j k A B $.
  ntp4vc-recursive-calls-definition $a |- (
    NTP4VCRecursiveCalls A B
  ) <-> (
    A. f e. A A. g e. A
      A. h e. ( NTP4VCMemory A )
        A. i e. B
          (
            (
              g =/= NTP4VCNull
              /\
              (
                NTP4VCIsTree
                  ( NTP4VCMemAccessor h ) i g f
              )
            )
            ->
            (
              g =/= NTP4VCNull
              /\
              (
                g =/= NTP4VCNull
                /\
                (
                  i =/= NTP4VCEmpty
                  /\
                  A. j e. B A. k e. B
                    (
                      (
                        NTP4VCSubtrees A B i j k
                      )
                      ->
                      (
                        NTP4VCRecursivePair
                          A B h i j k
                          (
                            (
                              ( NTP4VCMemAccessor h )
                              ` NTP4VCLeft
                            )
                            ` g
                          )
                          (
                            (
                              ( NTP4VCMemAccessor h )
                              ` NTP4VCRight
                            )
                            ` g
                          )
                          ( NTP4VCMemAccessor h )
                          g f
                      )
                    )
                )
              )
            )
          )
  ) $.
$}

ntp4vc-finish-location-definition $a |- (
  NTP4VCFinishLocation A B C D E F G H
) <-> (
  (
    NTP4VCRotated
      A F ( NTP4VCMemAccessor G )
      NTP4VCFinish H
  )
  ->
  (
    (
      NTP4VCRotated
        A F ( NTP4VCMemAccessor G )
        NTP4VCFinish H
    )
    /\
    (
      (
        (
          NTP4VCExt
            A ( NTP4VCFootprint D ) F
            ( NTP4VCMemAccessor G )
        )
        /\
        (
          NTP4VCIsTree F D E NTP4VCNull
        )
      )
      /\
      (
        (
          NTP4VCIsTree
            ( NTP4VCMemAccessor G )
            D E NTP4VCNull
        )
        ->
        (
          (
            NTP4VCIsTree
              ( NTP4VCMemAccessor G )
              D E NTP4VCNull
          )
          /\
          (
            NTP4VCUnchanged
              A
              ( NTP4VCMemAccessor C )
              ( NTP4VCMemAccessor G )
          )
          /\
          (
            NTP4VCWasMarked
              A D
              ( NTP4VCMemMark C )
              ( NTP4VCMemMark G )
          )
        )
      )
    )
  )
) $.

${
  $d f x A B C D E F $.
  ntp4vc-finish-memories-definition $a |- (
    NTP4VCFinishMemories A B C D E F
  ) <-> (
    A. f e. ( NTP4VCMemory A )
      (
        (
          (
            NTP4VCUnchanged
              A
              ( NTP4VCMemAccessor C )
              ( NTP4VCMemAccessor f )
          )
          /\
          (
            NTP4VCWasMarked
              A D
              ( NTP4VCMemMark C )
              ( NTP4VCMemMark f )
          )
        )
        ->
        (
          (
            NTP4VCRotated
              A F ( NTP4VCMemAccessor f )
              NTP4VCFinish NTP4VCNull
          )
          /\
          A. x e. A
            (
              NTP4VCFinishLocation
                A B C D E F f x
            )
        )
      )
  ) $.
$}

ntp4vc-top-finish-definition $a |- (
  NTP4VCTopFinish A B C D E
) <-> (
  (
    E =/= NTP4VCNull
    /\
    (
      NTP4VCIsTree
        ( NTP4VCMemAccessor C )
        D E NTP4VCNull
    )
  )
  /\
  (
    NTP4VCFinishMemories
      A B C D E ( NTP4VCMemAccessor C )
  )
) $.

ntp4vc-mark-tree-vc-definition $a |- (
  NTP4VCMarkTreeVC A B C D E
) <-> (
  (
    NTP4VCBlocObligation A
  )
  /\
  (
    NTP4VCRecursiveCalls A B
  )
  /\
  (
    NTP4VCTopFinish A B C D E
  )
) $.

${
  $d a b c d e f g h i j k l m n o p q r s t u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary source location carrier and null value. $)
  ntp4vc-location-carrier-nonempty $e |- L =/= (/) $.
  ntp4vc-null-location $e |- NTP4VCNull e. L $.

  $( Exact finite inductive location-labelled binary-tree datatype. $)
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

  $( Complete recursive source footprint definition. $)
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

  $( Complete recursive source is_tree definition. $)
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

  $( Source theorem parameters and assumptions. $)
  ntp4vc-memory-parameter $e |- M e. ( NTP4VCMemory L ) $.
  ntp4vc-tree-parameter $e |- R e. T $.
  ntp4vc-root-parameter $e |- P e. L $.

  ntp4vc-fact0 $e |- (
    NTP4VCIsTree
      ( NTP4VCMemAccessor M )
      R P NTP4VCNull
  ) $.

  ntp4vc-fact1 $e |- P =/= NTP4VCNull $.

  ntp4vc-pearl-verifythis-2016-tree-traversal-recursive-mark-tree-vc
    $a |- (
      NTP4VCMarkTreeVC L T M R P
    ) $.
$}
