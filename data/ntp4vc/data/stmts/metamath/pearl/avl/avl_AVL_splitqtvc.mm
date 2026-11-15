$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_splitqtvc: the AVL split verification condition states
  the selection, sequence-rebuilding, subtree decomposition, and bounded
  height-loss obligations for splitting an empty or nonempty AVL tree
  through the left, right, or current-node branch. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For the arbitrary source type parameter, U, V, W, S, and X are respectively
  the instantiated carriers t1 alpha, t2 alpha, t, selector, and tree alpha.
  A source m alpha record is represented exactly by an ordered pair in
  ( Word U X. ZZ ); P is m1, L is repr, M is seq_model, N is real_height, and
  O is the balanced subset. The tagged tree carrier, recursive equations,
  universal t'invariant, and t'inj law preserve the full abstract AVL model.

  F, G, H, I, and Q instantiate zero, op, measure, measure_closure, and
  agg measure_closure, with all source laws retained. SetMM words over U are
  exactly arbitrary finite zero-based source lists. Source views, options, and
  splits use disjoint tagged encodings; rebuilding and extension operations
  directly expand their source list definitions.

  R and T are the full typed relations selected and selection_possible, with
  selection_empty retained for every selector. The universal source match on
  part_base selector is split into its exhaustive Here, Left, and Right
  constructor cases. View matches are equivalent guarded cases, each option
  match is equality with its quantified tagged option, and every source let
  binding is expanded by substitution. The recursive result quantifiers over
  splits, abstract subtrees, options, and rebuilt trees retain their source
  scope, including the internal rebuilt-tree parameter and its exact
  zero-to-one height-loss bound.

  The unused inhabited source type part is conservatively extendible by a
  singleton carrier. All carriers and quantifiers retain their full source
  domains. Splitting the theorem's typed parameters and two assumptions into
  scoped essential hypotheses is bidirectionally equivalent to the source
  curried theorem. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAEmpty NTP4VCANode NTP4VCView
  NTP4VCNodeLeft NTP4VCNodeData NTP4VCNodeRight
  NTP4VCNodeHeight NTP4VCNodeSummary
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCNone NTP4VCSome NTP4VCOption
  NTP4VCSplitMk NTP4VCSplit NTP4VCSplitLeft
  NTP4VCSplitMiddle NTP4VCSplitRight
  NTP4VCOptionSeq NTP4VCRebuild
  NTP4VCLeftExtend NTP4VCRightExtend
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCSelected NTP4VCSelectionPossible NTP4VCBalance
$.

ntp4vc-aempty-syntax $a class NTP4VCAEmpty $.
ntp4vc-anode-syntax $a class ( NTP4VCANode A B C D E ) $.
ntp4vc-view-syntax $a class ( NTP4VCView A B C ) $.
ntp4vc-node-left-syntax $a class ( NTP4VCNodeLeft A ) $.
ntp4vc-node-data-syntax $a class ( NTP4VCNodeData A ) $.
ntp4vc-node-right-syntax $a class ( NTP4VCNodeRight A ) $.
ntp4vc-node-height-syntax $a class ( NTP4VCNodeHeight A ) $.
ntp4vc-node-summary-syntax $a class ( NTP4VCNodeSummary A ) $.

ntp4vc-tree-empty-syntax $a class NTP4VCTreeEmpty $.
ntp4vc-tree-node-syntax
  $a class ( NTP4VCTreeNode A B C D E ) $.

ntp4vc-none-syntax $a class NTP4VCNone $.
ntp4vc-some-syntax $a class ( NTP4VCSome A ) $.
ntp4vc-option-syntax $a class ( NTP4VCOption A ) $.

ntp4vc-split-mk-syntax $a class ( NTP4VCSplitMk A B C ) $.
ntp4vc-split-syntax $a class ( NTP4VCSplit A ) $.
ntp4vc-split-left-syntax $a class ( NTP4VCSplitLeft A ) $.
ntp4vc-split-middle-syntax $a class ( NTP4VCSplitMiddle A ) $.
ntp4vc-split-right-syntax $a class ( NTP4VCSplitRight A ) $.
ntp4vc-option-seq-syntax $a class ( NTP4VCOptionSeq A ) $.
ntp4vc-rebuild-syntax $a class ( NTP4VCRebuild A ) $.
ntp4vc-left-extend-syntax
  $a class ( NTP4VCLeftExtend A B C ) $.
ntp4vc-right-extend-syntax
  $a class ( NTP4VCRightExtend A B C ) $.

ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-selected-syntax $a wff ( NTP4VCSelected A B C ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A B C ) $.
ntp4vc-balance-syntax $a wff ( NTP4VCBalance A B C D ) $.

ntp4vc-aempty-def $a |- NTP4VCAEmpty = (/) $.

ntp4vc-anode-def $a |- ( NTP4VCANode A B C D E ) =
  <. 1 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

${
  $d h q s x y z A B C $.

  ntp4vc-view-def $a |- ( NTP4VCView A B C ) =
    { x |
      (
        x = NTP4VCAEmpty
        \/
        E. q e. B
          E. s e. A
            E. h e. B
              E. y e. NN0
                E. z e. C
                  x = ( NTP4VCANode q s h y z )
      )
    } $.
$}

ntp4vc-node-left-def $a |- ( NTP4VCNodeLeft A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-node-data-def $a |- ( NTP4VCNodeData A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-node-right-def $a |- ( NTP4VCNodeRight A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-node-height-def $a |- ( NTP4VCNodeHeight A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-node-summary-def $a |- ( NTP4VCNodeSummary A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-tree-empty-def $a |- NTP4VCTreeEmpty = <. 2 , (/) >. $.

ntp4vc-tree-node-def $a |- ( NTP4VCTreeNode A B C D E ) =
  <. 3 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

ntp4vc-none-def $a |- NTP4VCNone = (/) $.
ntp4vc-some-def $a |- ( NTP4VCSome A ) = <. 1 , A >. $.

${
  $d x y A $.

  ntp4vc-option-def $a |- ( NTP4VCOption A ) =
    { x |
      (
        x = NTP4VCNone
        \/
        E. y e. A x = ( NTP4VCSome y )
      )
    } $.
$}

ntp4vc-split-mk-def $a |- ( NTP4VCSplitMk A B C ) =
  <. A , <. B , C >. >. $.

${
  $d l o r x A $.

  ntp4vc-split-def $a |- ( NTP4VCSplit A ) =
    { x |
      E. l e. Word A
        E. o e. ( NTP4VCOption A )
          E. r e. Word A
            x = ( NTP4VCSplitMk l o r )
    } $.
$}

ntp4vc-split-left-def $a |- ( NTP4VCSplitLeft A ) =
  ( 1st ` A ) $.
ntp4vc-split-middle-def $a |- ( NTP4VCSplitMiddle A ) =
  ( 1st ` ( 2nd ` A ) ) $.
ntp4vc-split-right-def $a |- ( NTP4VCSplitRight A ) =
  ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-option-seq-def $a |- ( NTP4VCOptionSeq A ) =
  if ( A = NTP4VCNone , (/) , <" ( 2nd ` A ) "> ) $.

ntp4vc-rebuild-def $a |- ( NTP4VCRebuild A ) =
  (
    (
      ( NTP4VCSplitLeft A )
      ++
      ( NTP4VCOptionSeq ( NTP4VCSplitMiddle A ) )
    )
    ++
    ( NTP4VCSplitRight A )
  ) $.

ntp4vc-left-extend-def $a |- ( NTP4VCLeftExtend A B C ) =
  (
    NTP4VCSplitMk
      ( A ++ ( <" B "> ++ ( NTP4VCSplitLeft C ) ) )
      ( NTP4VCSplitMiddle C )
      ( NTP4VCSplitRight C )
  ) $.

ntp4vc-right-extend-def $a |- ( NTP4VCRightExtend A B C ) =
  (
    NTP4VCSplitMk
      ( NTP4VCSplitLeft A )
      ( NTP4VCSplitMiddle A )
      ( ( NTP4VCSplitRight A ) ++ ( <" B "> ++ C ) )
  ) $.

ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.
ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.
ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-selected-def $a |- (
  ( NTP4VCSelected A B C ) <-> <. A , B >. e. C
) $.

ntp4vc-selection-possible-def $a |- (
  ( NTP4VCSelectionPossible A B C ) <-> <. A , B >. e. C
) $.

ntp4vc-balance-def $a |- (
  ( NTP4VCBalance A B C D )
  <->
  (
    -u D
    <_
    ( ( NTP4VCHgt ( C ` A ) ) - ( NTP4VCHgt ( C ` B ) ) )
    /\
    (
      ( ( NTP4VCHgt ( C ` A ) ) - ( NTP4VCHgt ( C ` B ) ) )
      <_
      D
    )
  )
) $.


${
  $d d e h l m q r s u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  ntp4vc-t1-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-t2-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-t-carrier-nonempty $e |- W =/= (/) $.
  ntp4vc-selector-carrier-nonempty $e |- S =/= (/) $.

  ntp4vc-tree-empty-in-carrier $e |- NTP4VCTreeEmpty e. X $.
  ntp4vc-tree-node-closure $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      ( NTP4VCTreeNode l d r h m ) e. X $.
  ntp4vc-tree-exhaustive $e |- A. x e. X (
    x = NTP4VCTreeEmpty
    \/
    E. l e. X E. d e. U E. r e. X E. h e. NN0 E. m e. W
      x = ( NTP4VCTreeNode l d r h m )
  ) $.

  ntp4vc-m1-function $e |- P e. ( ( Word U X. ZZ ) ^m V ) $.
  ntp4vc-repr-function $e |- L e. ( X ^m V ) $.
  ntp4vc-seq-model-function $e |- M e. ( ( Word U ) ^m X ) $.
  ntp4vc-real-height-function $e |- N e. ( ZZ ^m X ) $.
  ntp4vc-balanced-predicate $e |- O C_ X $.

  ntp4vc-seq-model-empty $e |- ( M ` NTP4VCTreeEmpty ) = (/) $.
  ntp4vc-seq-model-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      (
        M ` ( NTP4VCTreeNode l d r h m )
      )
      =
      ( NTP4VCNodeModel ( M ` l ) d ( M ` r ) ) $.
  ntp4vc-real-height-empty $e |- ( N ` NTP4VCTreeEmpty ) = 0 $.
  ntp4vc-real-height-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      (
        N ` ( NTP4VCTreeNode l d r h m )
      )
      =
      (
        1 + if ( ( N ` l ) < ( N ` r ) , ( N ` r ) , ( N ` l ) )
      ) $.

  ntp4vc-zero-type $e |- F e. W $.
  ntp4vc-op-function $e |- G e. ( W ^m ( W X. W ) ) $.
  ntp4vc-measure-function $e |- H e. ( W ^m U ) $.
  ntp4vc-measure-closure-function $e |- I e. ( W ^m U ) $.
  ntp4vc-agg-measure-function $e |- Q e. ( W ^m Word U ) $.
  ntp4vc-op-associative $e |- A. x e. W A. y e. W A. z e. W
    (
      G ` <. x , ( G ` <. y , z >. ) >.
    )
    =
    (
      G ` <. ( G ` <. x , y >. ) , z >.
    ) $.
  ntp4vc-op-neutral $e |- A. x e. W (
    ( G ` <. x , F >. ) = x
    /\
    x = ( G ` <. F , x >. )
  ) $.
  ntp4vc-measure-closure-law $e |- A. x e. U
    ( I ` x ) = ( H ` x ) $.
  ntp4vc-aggregate-empty $e |- ( Q ` (/) ) = F $.
  ntp4vc-aggregate-singleton $e |- A. x e. U
    ( Q ` <" x "> ) = ( I ` x ) $.
  ntp4vc-aggregate-concatenation $e |- A. x e. Word U
    A. y e. Word U
      ( Q ` ( x ++ y ) )
      =
      ( G ` <. ( Q ` x ) , ( Q ` y ) >. ) $.

  ntp4vc-balanced-empty $e |- NTP4VCTreeEmpty e. O $.
  ntp4vc-balanced-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      (
        ( NTP4VCTreeNode l d r h m ) e. O
        <->
        (
          h = ( N ` ( NTP4VCTreeNode l d r h m ) )
          /\
          (
            m = ( Q ` ( M ` ( NTP4VCTreeNode l d r h m ) ) )
            /\
            (
              (
                -u E <_ ( ( N ` r ) - ( N ` l ) )
                /\
                ( ( N ` r ) - ( N ` l ) ) <_ E
              )
              /\
              ( l e. O /\ r e. O )
            )
          )
        )
      ) $.

  ntp4vc-t-invariant $e |- A. x e. V (
    (
      ( L ` x ) e. O
      /\
      ( NTP4VCSeq ( P ` x ) ) = ( M ` ( L ` x ) )
    )
    /\
    ( NTP4VCHgt ( P ` x ) ) = ( N ` ( L ` x ) )
  ) $.
  ntp4vc-t-injective $e |- A. x e. V A. y e. V (
    (
      ( L ` x ) = ( L ` y )
      /\
      ( P ` x ) = ( P ` y )
    )
    ->
    x = y
  ) $.

  ntp4vc-selected-relation $e |- R C_ ( S X. ( NTP4VCSplit U ) ) $.
  ntp4vc-selection-possible-relation
    $e |- T C_ ( S X. Word U ) $.
  ntp4vc-selection-empty-law $e |- A. x e. S (
    (
      NTP4VCSelectionPossible x (/) T
    )
    ->
    (
      NTP4VCSelected
        x ( NTP4VCSplitMk (/) NTP4VCNone (/) ) R
    )
  ) $.
  ntp4vc-balancing-positive-natural $e |- E e. NN $.

  $( Source theorem parameters A=s, B=t3, and C=o1. $)
  ntp4vc-s-type $e |- A e. S $.
  ntp4vc-t3-type $e |- B e. V $.
  ntp4vc-o1-view-type $e |- C e. ( NTP4VCView U V W ) $.

  ntp4vc-fact0 $e |- (
    NTP4VCSelectionPossible
      A ( NTP4VCSeq ( P ` B ) ) T
  ) $.

  ntp4vc-fact1 $e |- (
    (
      C = NTP4VCAEmpty
      /\
      (
        ( NTP4VCHgt ( P ` B ) ) = 0
        /\
        ( NTP4VCSeq ( P ` B ) ) = (/)
      )
    )
    \/
    (
      C =/= NTP4VCAEmpty
      /\
      (
        ( NTP4VCSeq ( P ` B ) )
        =
        (
          NTP4VCNodeModel
            ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
            ( NTP4VCNodeData C )
            ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
        )
        /\
        (
          ( NTP4VCNodeSummary C )
          =
          ( Q ` ( NTP4VCSeq ( P ` B ) ) )
          /\
          (
            (
              NTP4VCBalance
                ( NTP4VCNodeLeft C )
                ( NTP4VCNodeRight C )
                P E
            )
            /\
            (
              ( NTP4VCHgt ( P ` B ) ) = ( NTP4VCNodeHeight C )
              /\
              (
                ( NTP4VCNodeHeight C )
                =
                (
                  1
                  +
                  if
                  (
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeLeft C ) )
                    )
                    <
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeRight C ) )
                    ) ,
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeRight C ) )
                    ) ,
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeLeft C ) )
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

  ntp4vc-pearl-avl-split-vc $a |- (
    (
      C = NTP4VCAEmpty
      /\
      (
        (
          (
            NTP4VCSelected
              A ( NTP4VCSplitMk (/) NTP4VCNone (/) ) R
          )
          /\
          (
            NTP4VCRebuild
              ( NTP4VCSplitMk (/) NTP4VCNone (/) )
          )
          =
          ( NTP4VCSeq ( P ` B ) )
        )
        /\
        (
          ( NTP4VCSeq ( P ` B ) )
          =
          (
            NTP4VCSplitLeft
              ( NTP4VCSplitMk (/) NTP4VCNone (/) )
          )
          /\
          (
            ( NTP4VCSeq ( P ` B ) )
            =
            (
              NTP4VCSplitRight
                ( NTP4VCSplitMk (/) NTP4VCNone (/) )
            )
            /\
            (
              NTP4VCSplitMiddle
                ( NTP4VCSplitMk (/) NTP4VCNone (/) )
            )
            =
            NTP4VCNone
          )
        )
      )
    )
    \/
    (
      C =/= NTP4VCAEmpty
      /\
      (
        (
          (
            NTP4VCSelectionPossible
              A
              (
                NTP4VCNodeModel
                  ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                  ( NTP4VCNodeData C )
                  ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
              )
              T
          )
          /\
          (
            (
              Q ` ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
            )
            =
            (
              Q ` ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
            )
            /\
            (
              Q ` ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
            )
            =
            (
              Q ` ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
            )
          )
        )
        /\
        (
          (
            (
              NTP4VCSelected
                A
                (
                  NTP4VCSplitMk
                    ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                    ( NTP4VCSome ( NTP4VCNodeData C ) )
                    ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                )
                R
            )
            ->
            (
              (
                (
                  NTP4VCSelected
                    A
                    (
                      NTP4VCSplitMk
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                        ( NTP4VCSome ( NTP4VCNodeData C ) )
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                    )
                    R
                )
                /\
                (
                  NTP4VCRebuild
                    (
                      NTP4VCSplitMk
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                        ( NTP4VCSome ( NTP4VCNodeData C ) )
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                    )
                )
                =
                ( NTP4VCSeq ( P ` B ) )
              )
              /\
              (
                ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                =
                (
                  NTP4VCSplitLeft
                    (
                      NTP4VCSplitMk
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                        ( NTP4VCSome ( NTP4VCNodeData C ) )
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                    )
                )
                /\
                (
                  ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                  =
                  (
                    NTP4VCSplitRight
                      (
                        NTP4VCSplitMk
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                          ( NTP4VCSome ( NTP4VCNodeData C ) )
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                      )
                  )
                  /\
                  (
                    NTP4VCSplitMiddle
                      (
                        NTP4VCSplitMk
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                          ( NTP4VCSome ( NTP4VCNodeData C ) )
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                      )
                  )
                  =
                  ( NTP4VCSome ( NTP4VCNodeData C ) )
                )
              )
            )
          )
          /\
          (
            A. x e. S
              (
                (
                  (
                    NTP4VCSelectionPossible
                      x
                      ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                      T
                  )
                  /\
                  A. e e. ( NTP4VCSplit U )
                    (
                      (
                        ( NTP4VCSelected x e R )
                        /\
                        (
                          ( NTP4VCRebuild e )
                          =
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                        )
                      )
                      ->
                      (
                        NTP4VCSelected
                          A
                          (
                            NTP4VCRightExtend
                              e
                              ( NTP4VCNodeData C )
                              ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                          )
                          R
                      )
                    )
                )
                ->
                (
                  (
                    (
                      0 <_ ( NTP4VCHgt ( P ` B ) )
                      /\
                      (
                        NTP4VCHgt ( P ` ( NTP4VCNodeLeft C ) )
                      )
                      <
                      ( NTP4VCHgt ( P ` B ) )
                    )
                    /\
                    (
                      NTP4VCSelectionPossible
                        x
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                        T
                    )
                  )
                  /\
                  A. e e. ( NTP4VCSplit U )
                    A. l e. V
                      A. u e. ( NTP4VCOption U )
                        A. r e. V
                          (
                            (
                              (
                                (
                                  ( NTP4VCSelected x e R )
                                  /\
                                  (
                                    ( NTP4VCRebuild e )
                                    =
                                    (
                                      NTP4VCSeq
                                        ( P ` ( NTP4VCNodeLeft C ) )
                                    )
                                  )
                                )
                                /\
                                (
                                  ( NTP4VCSeq ( P ` l ) )
                                  =
                                  ( NTP4VCSplitLeft e )
                                )
                              )
                              /\
                              (
                                ( NTP4VCSeq ( P ` r ) )
                                =
                                ( NTP4VCSplitRight e )
                              )
                              /\
                              ( NTP4VCSplitMiddle e ) = u
                            )
                            ->
                            A. z e. V
                              (
                                (
                                  (
                                    ( NTP4VCSeq ( P ` z ) )
                                    =
                                    (
                                      NTP4VCNodeModel
                                        ( NTP4VCSeq ( P ` r ) )
                                        ( NTP4VCNodeData C )
                                        (
                                          NTP4VCSeq
                                            ( P ` ( NTP4VCNodeRight C ) )
                                        )
                                    )
                                  )
                                  /\
                                  (
                                    0
                                    <_
                                    (
                                      (
                                        1
                                        +
                                        if
                                        (
                                          (
                                            NTP4VCHgt ( P ` r )
                                          )
                                          <
                                          (
                                            NTP4VCHgt
                                              (
                                                P `
                                                ( NTP4VCNodeRight C )
                                              )
                                          ) ,
                                          (
                                            NTP4VCHgt
                                              (
                                                P `
                                                ( NTP4VCNodeRight C )
                                              )
                                          ) ,
                                          ( NTP4VCHgt ( P ` r ) )
                                        )
                                      )
                                      -
                                      ( NTP4VCHgt ( P ` z ) )
                                    )
                                    /\
                                    (
                                      (
                                        (
                                          1
                                          +
                                          if
                                          (
                                            (
                                              NTP4VCHgt ( P ` r )
                                            )
                                            <
                                            (
                                              NTP4VCHgt
                                                (
                                                  P `
                                                  ( NTP4VCNodeRight C )
                                                )
                                            ) ,
                                            (
                                              NTP4VCHgt
                                                (
                                                  P `
                                                  ( NTP4VCNodeRight C )
                                                )
                                            ) ,
                                            ( NTP4VCHgt ( P ` r ) )
                                          )
                                        )
                                        -
                                        ( NTP4VCHgt ( P ` z ) )
                                      )
                                      <_
                                      1
                                    )
                                  )
                                )
                                ->
                                (
                                  (
                                    (
                                      NTP4VCSelected
                                        A
                                        (
                                          NTP4VCRightExtend
                                            e
                                            ( NTP4VCNodeData C )
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeRight C )
                                                )
                                            )
                                        )
                                        R
                                    )
                                    /\
                                    (
                                      NTP4VCRebuild
                                        (
                                          NTP4VCRightExtend
                                            e
                                            ( NTP4VCNodeData C )
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeRight C )
                                                )
                                            )
                                        )
                                    )
                                    =
                                    ( NTP4VCSeq ( P ` B ) )
                                  )
                                  /\
                                  (
                                    ( NTP4VCSeq ( P ` l ) )
                                    =
                                    (
                                      NTP4VCSplitLeft
                                        (
                                          NTP4VCRightExtend
                                            e
                                            ( NTP4VCNodeData C )
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeRight C )
                                                )
                                            )
                                        )
                                    )
                                    /\
                                    (
                                      ( NTP4VCSeq ( P ` z ) )
                                      =
                                      (
                                        NTP4VCSplitRight
                                          (
                                            NTP4VCRightExtend
                                              e
                                              ( NTP4VCNodeData C )
                                              (
                                                NTP4VCSeq
                                                  (
                                                    P `
                                                    ( NTP4VCNodeRight C )
                                                  )
                                              )
                                          )
                                      )
                                      /\
                                      (
                                        NTP4VCSplitMiddle
                                          (
                                            NTP4VCRightExtend
                                              e
                                              ( NTP4VCNodeData C )
                                              (
                                                NTP4VCSeq
                                                  (
                                                    P `
                                                    ( NTP4VCNodeRight C )
                                                  )
                                              )
                                          )
                                      )
                                      =
                                      u
                                    )
                                  )
                                )
                              )
                          )
                )
              )
            /\
            A. x e. S
              (
                (
                  (
                    NTP4VCSelectionPossible
                      x
                      ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                      T
                  )
                  /\
                  A. e e. ( NTP4VCSplit U )
                    (
                      (
                        ( NTP4VCSelected x e R )
                        /\
                        (
                          ( NTP4VCRebuild e )
                          =
                          ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                        )
                      )
                      ->
                      (
                        NTP4VCSelected
                          A
                          (
                            NTP4VCLeftExtend
                              ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft C ) ) )
                              ( NTP4VCNodeData C )
                              e
                          )
                          R
                      )
                    )
                )
                ->
                (
                  (
                    (
                      0 <_ ( NTP4VCHgt ( P ` B ) )
                      /\
                      (
                        NTP4VCHgt ( P ` ( NTP4VCNodeRight C ) )
                      )
                      <
                      ( NTP4VCHgt ( P ` B ) )
                    )
                    /\
                    (
                      NTP4VCSelectionPossible
                        x
                        ( NTP4VCSeq ( P ` ( NTP4VCNodeRight C ) ) )
                        T
                    )
                  )
                  /\
                  A. e e. ( NTP4VCSplit U )
                    A. l e. V
                      A. u e. ( NTP4VCOption U )
                        A. r e. V
                          (
                            (
                              (
                                (
                                  ( NTP4VCSelected x e R )
                                  /\
                                  (
                                    ( NTP4VCRebuild e )
                                    =
                                    (
                                      NTP4VCSeq
                                        ( P ` ( NTP4VCNodeRight C ) )
                                    )
                                  )
                                )
                                /\
                                (
                                  ( NTP4VCSeq ( P ` l ) )
                                  =
                                  ( NTP4VCSplitLeft e )
                                )
                              )
                              /\
                              (
                                ( NTP4VCSeq ( P ` r ) )
                                =
                                ( NTP4VCSplitRight e )
                              )
                              /\
                              ( NTP4VCSplitMiddle e ) = u
                            )
                            ->
                            A. z e. V
                              (
                                (
                                  (
                                    ( NTP4VCSeq ( P ` z ) )
                                    =
                                    (
                                      NTP4VCNodeModel
                                        (
                                          NTP4VCSeq
                                            ( P ` ( NTP4VCNodeLeft C ) )
                                        )
                                        ( NTP4VCNodeData C )
                                        ( NTP4VCSeq ( P ` l ) )
                                    )
                                  )
                                  /\
                                  (
                                    0
                                    <_
                                    (
                                      (
                                        1
                                        +
                                        if
                                        (
                                          (
                                            NTP4VCHgt
                                              (
                                                P `
                                                ( NTP4VCNodeLeft C )
                                              )
                                          )
                                          <
                                          ( NTP4VCHgt ( P ` l ) ) ,
                                          ( NTP4VCHgt ( P ` l ) ) ,
                                          (
                                            NTP4VCHgt
                                              (
                                                P `
                                                ( NTP4VCNodeLeft C )
                                              )
                                          )
                                        )
                                      )
                                      -
                                      ( NTP4VCHgt ( P ` z ) )
                                    )
                                    /\
                                    (
                                      (
                                        (
                                          1
                                          +
                                          if
                                          (
                                            (
                                              NTP4VCHgt
                                                (
                                                  P `
                                                  ( NTP4VCNodeLeft C )
                                                )
                                            )
                                            <
                                            ( NTP4VCHgt ( P ` l ) ) ,
                                            ( NTP4VCHgt ( P ` l ) ) ,
                                            (
                                              NTP4VCHgt
                                                (
                                                  P `
                                                  ( NTP4VCNodeLeft C )
                                                )
                                            )
                                          )
                                        )
                                        -
                                        ( NTP4VCHgt ( P ` z ) )
                                      )
                                      <_
                                      1
                                    )
                                  )
                                )
                                ->
                                (
                                  (
                                    (
                                      NTP4VCSelected
                                        A
                                        (
                                          NTP4VCLeftExtend
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeLeft C )
                                                )
                                            )
                                            ( NTP4VCNodeData C )
                                            e
                                        )
                                        R
                                    )
                                    /\
                                    (
                                      NTP4VCRebuild
                                        (
                                          NTP4VCLeftExtend
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeLeft C )
                                                )
                                            )
                                            ( NTP4VCNodeData C )
                                            e
                                        )
                                    )
                                    =
                                    ( NTP4VCSeq ( P ` B ) )
                                  )
                                  /\
                                  (
                                    ( NTP4VCSeq ( P ` z ) )
                                    =
                                    (
                                      NTP4VCSplitLeft
                                        (
                                          NTP4VCLeftExtend
                                            (
                                              NTP4VCSeq
                                                (
                                                  P `
                                                  ( NTP4VCNodeLeft C )
                                                )
                                            )
                                            ( NTP4VCNodeData C )
                                            e
                                        )
                                    )
                                    /\
                                    (
                                      ( NTP4VCSeq ( P ` r ) )
                                      =
                                      (
                                        NTP4VCSplitRight
                                          (
                                            NTP4VCLeftExtend
                                              (
                                                NTP4VCSeq
                                                  (
                                                    P `
                                                    ( NTP4VCNodeLeft C )
                                                  )
                                              )
                                              ( NTP4VCNodeData C )
                                              e
                                          )
                                      )
                                      /\
                                      (
                                        NTP4VCSplitMiddle
                                          (
                                            NTP4VCLeftExtend
                                              (
                                                NTP4VCSeq
                                                  (
                                                    P `
                                                    ( NTP4VCNodeLeft C )
                                                  )
                                              )
                                              ( NTP4VCNodeData C )
                                              e
                                          )
                                      )
                                      =
                                      u
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
