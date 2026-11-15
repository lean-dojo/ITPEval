$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_extractqtvc: the AVL extract verification condition
  states the selection, sequence-rebuilding, height-loss, and balance
  obligations for extracting an optional element through an empty or
  nonempty AVL tree view. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For the arbitrary source type parameter, U, V, W, S, and X are
  respectively the instantiated carriers t1 alpha, t2 alpha, t, selector,
  and tree alpha. A source m alpha record is represented exactly by an
  ordered pair in ( Word U X. ZZ ); P is m1, L is repr, M is seq_model,
  N is real_height, and O is the balanced subset. The tagged tree carrier
  is required to contain exactly Empty and every finite Node term; the
  recursive equations for M, N, and O reproduce the source definitions.
  The universal t'invariant and t'inj laws are imposed on every element
  of V, preserving the full AVL representation constraints on P.

  F, G, H, I, and Q instantiate zero, op, measure, measure_closure, and
  agg measure_closure. Their full monoid, empty, singleton, concatenation,
  and pointwise closure laws are stated below. The polymorphic source agg
  at types not occurring in this verification condition is a conservative
  extension: on every such carrier it is exactly the finite fold induced
  by F and G. Thus retaining its U-instance is bidirectionally
  model-extensible and neither strengthens nor weakens this artifact.

  SetMM words over U are exactly arbitrary finite zero-based source lists.
  The source option, split, and view datatypes are represented by disjoint
  tagged encodings, with their constructors and projections expanded below.
  NTP4VCRebuild, NTP4VCLeftExtend, NTP4VCRightExtend, and NTP4VCNodeModel
  directly encode the corresponding source list operations.

  The proposition-valued source functions selected and selection_possible
  are relations R and T on their full typed products, constrained by the
  source selection_empty law for every selector. The source universal
  match over part_base selector is split into its Here, Left, and Right
  constructor cases; this is bidirectionally equivalent over the disjoint
  exhaustive datatype encoding. Matches on views and options are likewise
  rendered by equivalent guarded cases, with the option match in each
  recursive result reduced to equality with the quantified option. Source
  let expressions are expanded by substitution. The unused inhabited
  source type part is conservatively extendible by a singleton carrier.

  Every selector, abstract-tree, split, option, word, natural, and integer
  quantifier retains its full source domain. Splitting the theorem's typed
  parameters and two assumptions into scoped essential hypotheses is
  bidirectionally equivalent to the source curried theorem. The final $a
  declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
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
  NTP4VCSelected NTP4VCSelectionPossible
  NTP4VCBalance NTP4VCExtendedBalance NTP4VCHeightLoss
  NTP4VCRebuildHeight NTP4VCHereCandidate NTP4VCResult
  NTP4VCLeftBranch NTP4VCRightBranch NTP4VCHereBranch
  NTP4VCEmptyConclusion NTP4VCNodeConclusion
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

ntp4vc-split-mk-syntax
  $a class ( NTP4VCSplitMk A B C ) $.
ntp4vc-split-syntax $a class ( NTP4VCSplit A ) $.
ntp4vc-split-left-syntax
  $a class ( NTP4VCSplitLeft A ) $.
ntp4vc-split-middle-syntax
  $a class ( NTP4VCSplitMiddle A ) $.
ntp4vc-split-right-syntax
  $a class ( NTP4VCSplitRight A ) $.
ntp4vc-option-seq-syntax
  $a class ( NTP4VCOptionSeq A ) $.
ntp4vc-rebuild-syntax $a class ( NTP4VCRebuild A ) $.
ntp4vc-left-extend-syntax
  $a class ( NTP4VCLeftExtend A B C ) $.
ntp4vc-right-extend-syntax
  $a class ( NTP4VCRightExtend A B C ) $.

ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax
  $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-selected-syntax
  $a wff ( NTP4VCSelected A B C ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A B C ) $.
ntp4vc-balance-syntax
  $a wff ( NTP4VCBalance A B C D ) $.
ntp4vc-extended-balance-syntax
  $a wff ( NTP4VCExtendedBalance A B C D ) $.
ntp4vc-height-loss-syntax
  $a wff ( NTP4VCHeightLoss A B C ) $.
ntp4vc-rebuild-height-syntax
  $a wff ( NTP4VCRebuildHeight A B C D E F ) $.
ntp4vc-here-candidate-syntax
  $a wff ( NTP4VCHereCandidate A B C D ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D E F G ) $.
ntp4vc-left-branch-syntax
  $a wff ( NTP4VCLeftBranch A B C D E F G H I J K L ) $.
ntp4vc-right-branch-syntax
  $a wff ( NTP4VCRightBranch A B C D E F G H I J K L ) $.
ntp4vc-here-branch-syntax
  $a wff ( NTP4VCHereBranch A B C D E F G H I ) $.
ntp4vc-empty-conclusion-syntax
  $a wff ( NTP4VCEmptyConclusion A B C D ) $.
ntp4vc-node-conclusion-syntax
  $a wff ( NTP4VCNodeConclusion A B C D E F G H I J K ) $.

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
  if (
    A = NTP4VCNone ,
    (/) ,
    <" ( 2nd ` A ) ">
  ) $.

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
      (
        A
        ++
        ( <" B "> ++ ( NTP4VCSplitLeft C ) )
      )
      ( NTP4VCSplitMiddle C )
      ( NTP4VCSplitRight C )
  ) $.

ntp4vc-right-extend-def $a |- ( NTP4VCRightExtend A B C ) =
  (
    NTP4VCSplitMk
      ( NTP4VCSplitLeft A )
      ( NTP4VCSplitMiddle A )
      (
        ( NTP4VCSplitRight A )
        ++
        ( <" B "> ++ C )
      )
  ) $.

ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.

ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.

ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-selected-def $a |- (
  ( NTP4VCSelected A B C )
  <->
  <. A , B >. e. C
) $.

ntp4vc-selection-possible-def $a |- (
  ( NTP4VCSelectionPossible A B C )
  <->
  <. A , B >. e. C
) $.

ntp4vc-balance-def $a |- (
  ( NTP4VCBalance A B C D )
  <->
  (
    -u D
    <_
    (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    /\
    (
      (
        ( NTP4VCHgt ( C ` A ) )
        -
        ( NTP4VCHgt ( C ` B ) )
      )
      <_
      D
    )
  )
) $.

ntp4vc-extended-balance-def $a |- (
  ( NTP4VCExtendedBalance A B C D )
  <->
  (
    ( -u D - 1 )
    <_
    (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    /\
    (
      (
        ( NTP4VCHgt ( C ` A ) )
        -
        ( NTP4VCHgt ( C ` B ) )
      )
      <_
      ( D + 1 )
    )
  )
) $.

ntp4vc-height-loss-def $a |- (
  ( NTP4VCHeightLoss A B C )
  <->
  (
    (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    <_
    1
    /\
    0
    <_
    (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
  )
) $.

ntp4vc-rebuild-height-def $a |- (
  ( NTP4VCRebuildHeight A B C D E F )
  <->
  (
    ( NTP4VCSeq ( E ` A ) )
    =
    (
      NTP4VCNodeModel
        ( NTP4VCSeq ( E ` B ) )
        C
        ( NTP4VCSeq ( E ` D ) )
    )
    /\
    (
      (
        0
        <_
        (
          (
            1
            +
            if
            (
              ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` D ) ) ,
              ( NTP4VCHgt ( E ` D ) ) ,
              ( NTP4VCHgt ( E ` B ) )
            )
          )
          -
          ( NTP4VCHgt ( E ` A ) )
        )
        /\
        (
          (
            (
              1
              +
              if
              (
                ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` D ) ) ,
                ( NTP4VCHgt ( E ` D ) ) ,
                ( NTP4VCHgt ( E ` B ) )
              )
            )
            -
            ( NTP4VCHgt ( E ` A ) )
          )
          <_
          1
        )
      )
      /\
      (
        ( NTP4VCBalance B D E F )
        ->
        (
          1
          +
          if
          (
            ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` D ) ) ,
            ( NTP4VCHgt ( E ` D ) ) ,
            ( NTP4VCHgt ( E ` B ) )
          )
        )
        =
        ( NTP4VCHgt ( E ` A ) )
      )
    )
  )
) $.

ntp4vc-here-candidate-def $a |- (
  ( NTP4VCHereCandidate A B C D )
  <->
  (
    ( NTP4VCSeq ( D ` A ) )
    =
    (
      ( NTP4VCSeq ( D ` B ) )
      ++
      ( NTP4VCSeq ( D ` C ) )
    )
    /\
    (
      (
        (
          1
          +
          if
          (
            ( NTP4VCHgt ( D ` B ) ) < ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` B ) )
          )
        )
        -
        ( NTP4VCHgt ( D ` A ) )
      )
      <_
      1
      /\
      0
      <_
      (
        (
          1
          +
          if
          (
            ( NTP4VCHgt ( D ` B ) ) < ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` B ) )
          )
        )
        -
        ( NTP4VCHgt ( D ` A ) )
      )
    )
  )
) $.

ntp4vc-result-def $a |- (
  ( NTP4VCResult A B C D E F G )
  <->
  (
    (
      ( NTP4VCSelected A B G )
      /\
      ( NTP4VCRebuild B ) = ( NTP4VCSeq ( F ` C ) )
    )
    /\
    (
      ( NTP4VCSeq ( F ` D ) )
      =
      (
        ( NTP4VCSplitLeft B )
        ++
        ( NTP4VCSplitRight B )
      )
      /\
      (
        ( NTP4VCHeightLoss C D F )
        /\
        ( NTP4VCSplitMiddle B ) = E
      )
    )
  )
) $.

${
  $d q r x y z A B C D E F G H I J K L $.

  ntp4vc-left-branch-def $a |- (
    ( NTP4VCLeftBranch A B C D E F G H I J K L )
    <->
    (
      (
        (
          0 <_ ( NTP4VCHgt ( G ` F ) )
          /\
          ( NTP4VCHgt ( G ` C ) ) < ( NTP4VCHgt ( G ` F ) )
        )
        /\
        (
          NTP4VCSelectionPossible
            B ( NTP4VCSeq ( G ` C ) ) J
        )
      )
      /\
      A. x e. ( NTP4VCSplit K )
        A. y e. ( NTP4VCOption K )
          A. z e. L
            (
              (
                (
                  (
                    ( NTP4VCSelected B x I )
                    /\
                    ( NTP4VCRebuild x ) = ( NTP4VCSeq ( G ` C ) )
                  )
                  /\
                  (
                    ( NTP4VCSeq ( G ` z ) )
                    =
                    (
                      ( NTP4VCSplitLeft x )
                      ++
                      ( NTP4VCSplitRight x )
                    )
                  )
                )
                /\
                (
                  ( NTP4VCHeightLoss C z G )
                  /\
                  ( NTP4VCSplitMiddle x ) = y
                )
              )
              ->
              (
                ( NTP4VCExtendedBalance z E G H )
                /\
                A. q e. L
                  (
                    ( NTP4VCRebuildHeight q z D E G H )
                    ->
                    (
                      NTP4VCResult
                        A
                        (
                          NTP4VCRightExtend
                            x D ( NTP4VCSeq ( G ` E ) )
                        )
                        F q y G I
                    )
                  )
              )
            )
    )
  ) $.
$}

${
  $d q r x y z A B C D E F G H I J K L $.

  ntp4vc-right-branch-def $a |- (
    ( NTP4VCRightBranch A B C D E F G H I J K L )
    <->
    (
      (
        (
          0 <_ ( NTP4VCHgt ( G ` F ) )
          /\
          ( NTP4VCHgt ( G ` E ) ) < ( NTP4VCHgt ( G ` F ) )
        )
        /\
        (
          NTP4VCSelectionPossible
            B ( NTP4VCSeq ( G ` E ) ) J
        )
      )
      /\
      A. x e. ( NTP4VCSplit K )
        A. y e. ( NTP4VCOption K )
          A. z e. L
            (
              (
                (
                  (
                    ( NTP4VCSelected B x I )
                    /\
                    ( NTP4VCRebuild x ) = ( NTP4VCSeq ( G ` E ) )
                  )
                  /\
                  (
                    ( NTP4VCSeq ( G ` z ) )
                    =
                    (
                      ( NTP4VCSplitLeft x )
                      ++
                      ( NTP4VCSplitRight x )
                    )
                  )
                )
                /\
                (
                  ( NTP4VCHeightLoss E z G )
                  /\
                  ( NTP4VCSplitMiddle x ) = y
                )
              )
              ->
              (
                ( NTP4VCExtendedBalance C z G H )
                /\
                A. q e. L
                  (
                    ( NTP4VCRebuildHeight q C D z G H )
                    ->
                    (
                      NTP4VCResult
                        A
                        (
                          NTP4VCLeftExtend
                            ( NTP4VCSeq ( G ` C ) ) D x
                        )
                        F q y G I
                    )
                  )
              )
            )
    )
  ) $.
$}

${
  $d q A B C D E F G H I $.

  ntp4vc-here-branch-def $a |- (
    ( NTP4VCHereBranch A B C D E F G H I )
    <->
    (
      ( NTP4VCBalance B D F G )
      /\
      A. q e. I
        (
          ( NTP4VCHereCandidate q B D F )
          ->
          (
            NTP4VCResult
              A
              (
                NTP4VCSplitMk
                  ( NTP4VCSeq ( F ` B ) )
                  ( NTP4VCSome C )
                  ( NTP4VCSeq ( F ` D ) )
              )
              E q ( NTP4VCSome C ) F H
          )
        )
    )
  ) $.
$}

ntp4vc-empty-conclusion-def $a |- (
  ( NTP4VCEmptyConclusion A B C D )
  <->
  (
    (
      (
        NTP4VCSelected
          A
          ( NTP4VCSplitMk (/) NTP4VCNone (/) )
          D
      )
      /\
      (
        NTP4VCRebuild
          ( NTP4VCSplitMk (/) NTP4VCNone (/) )
      )
      =
      ( NTP4VCSeq ( C ` B ) )
    )
    /\
    (
      ( NTP4VCSeq ( C ` B ) )
      =
      (
        (
          NTP4VCSplitLeft
            ( NTP4VCSplitMk (/) NTP4VCNone (/) )
        )
        ++
        (
          NTP4VCSplitRight
            ( NTP4VCSplitMk (/) NTP4VCNone (/) )
        )
      )
      /\
      (
        ( NTP4VCHeightLoss B B C )
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
) $.

${
  $d e q r x A B C D E F G H I J K $.

  ntp4vc-node-conclusion-def $a |- (
    ( NTP4VCNodeConclusion A B C D E F G H I J K )
    <->
    (
      (
        (
          NTP4VCSelectionPossible
            A
            (
              NTP4VCNodeModel
                (
                  NTP4VCSeq
                    ( D ` ( NTP4VCNodeLeft C ) )
                )
                ( NTP4VCNodeData C )
                (
                  NTP4VCSeq
                    ( D ` ( NTP4VCNodeRight C ) )
                )
            )
            H
        )
        /\
        (
          (
            E ` ( NTP4VCSeq ( D ` ( NTP4VCNodeLeft C ) ) )
          )
          =
          (
            E ` ( NTP4VCSeq ( D ` ( NTP4VCNodeLeft C ) ) )
          )
        )
      )
      /\
      (
        (
          E ` ( NTP4VCSeq ( D ` ( NTP4VCNodeRight C ) ) )
        )
        =
        (
          E ` ( NTP4VCSeq ( D ` ( NTP4VCNodeRight C ) ) )
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
                  (
                    NTP4VCSeq
                      ( D ` ( NTP4VCNodeLeft C ) )
                  )
                  ( NTP4VCSome ( NTP4VCNodeData C ) )
                  (
                    NTP4VCSeq
                      ( D ` ( NTP4VCNodeRight C ) )
                  )
              )
              G
          )
          ->
          (
            NTP4VCHereBranch
              A
              ( NTP4VCNodeLeft C )
              ( NTP4VCNodeData C )
              ( NTP4VCNodeRight C )
              B D F G K
          )
        )
        /\
        (
          A. x e. I
            (
              (
                (
                  NTP4VCSelectionPossible
                    x
                    (
                      NTP4VCSeq
                        ( D ` ( NTP4VCNodeLeft C ) )
                    )
                    H
                )
                /\
                A. e e. ( NTP4VCSplit J )
                  (
                    (
                      ( NTP4VCSelected x e G )
                      /\
                      (
                        ( NTP4VCRebuild e )
                        =
                        (
                          NTP4VCSeq
                            ( D ` ( NTP4VCNodeLeft C ) )
                        )
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
                            (
                              NTP4VCSeq
                                ( D ` ( NTP4VCNodeRight C ) )
                            )
                        )
                        G
                    )
                  )
              )
              ->
              (
                NTP4VCLeftBranch
                  A x
                  ( NTP4VCNodeLeft C )
                  ( NTP4VCNodeData C )
                  ( NTP4VCNodeRight C )
                  B D F G H J K
              )
            )
          /\
          A. x e. I
            (
              (
                (
                  NTP4VCSelectionPossible
                    x
                    (
                      NTP4VCSeq
                        ( D ` ( NTP4VCNodeRight C ) )
                    )
                    H
                )
                /\
                A. e e. ( NTP4VCSplit J )
                  (
                    (
                      ( NTP4VCSelected x e G )
                      /\
                      (
                        ( NTP4VCRebuild e )
                        =
                        (
                          NTP4VCSeq
                            ( D ` ( NTP4VCNodeRight C ) )
                        )
                      )
                    )
                    ->
                    (
                      NTP4VCSelected
                        A
                        (
                          NTP4VCLeftExtend
                            (
                              NTP4VCSeq
                                ( D ` ( NTP4VCNodeLeft C ) )
                            )
                            ( NTP4VCNodeData C )
                            e
                        )
                        G
                    )
                  )
              )
              ->
              (
                NTP4VCRightBranch
                  A x
                  ( NTP4VCNodeLeft C )
                  ( NTP4VCNodeData C )
                  ( NTP4VCNodeRight C )
                  B D F G H J K
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d d e h l m q r s u v w x y z
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source carriers and the exact tagged finite-tree datatype. $)
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

  $( Source records and abstract-tree functions. $)
  ntp4vc-m1-function $e |- P e. ( ( Word U X. ZZ ) ^m V ) $.
  ntp4vc-repr-function $e |- L e. ( X ^m V ) $.
  ntp4vc-seq-model-function $e |- M e. ( ( Word U ) ^m X ) $.
  ntp4vc-real-height-function $e |- N e. ( ZZ ^m X ) $.
  ntp4vc-balanced-predicate $e |- O C_ X $.

  $( Exact recursive equations for seq_model and real_height. $)
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
        1
        +
        if ( ( N ` l ) < ( N ` r ) , ( N ` r ) , ( N ` l ) )
      ) $.

  $( Source monoid, measure, measure_closure, and aggregate laws. $)
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
    (
      G ` <. x , F >.
    )
    =
    x
    /\
    x
    =
    (
      G ` <. F , x >.
    )
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
      (
        G ` <. ( Q ` x ) , ( Q ` y ) >.
      ) $.

  $( Exact recursive balanced definition. $)
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
                -u E
                <_
                ( ( N ` r ) - ( N ` l ) )
                /\
                ( ( N ` r ) - ( N ` l ) ) <_ E
              )
              /\
              ( l e. O /\ r e. O )
            )
          )
        )
      ) $.

  $( Universal source t'invariant and t'inj laws. $)
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

  $( Predicate-valued relations and the full source selection_empty law. $)
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
        x
        ( NTP4VCSplitMk (/) NTP4VCNone (/) )
        R
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

  $( The source fact1 view match, with all let-bound heights expanded. $)
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

  ntp4vc-pearl-avl-extract-vc $a |- (
    (
      C = NTP4VCAEmpty
      /\
      ( NTP4VCEmptyConclusion A B P R )
    )
    \/
    (
      C =/= NTP4VCAEmpty
      /\
      (
        NTP4VCNodeConclusion
          A B C P Q E R T S U V
      )
    )
  ) $.
$}
