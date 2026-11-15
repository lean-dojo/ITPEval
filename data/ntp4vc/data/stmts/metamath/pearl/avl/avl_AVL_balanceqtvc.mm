$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_balanceqtvc: the AVL balance verification condition
  states the height, case-analysis, rotation, and reconstructed-tree
  obligations for rebalancing two abstract AVL subtrees. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  For the arbitrary source type parameter, U, V, and W are respectively the
  instantiated carriers t1 alpha, t2 alpha, and t. A source m alpha record is
  represented exactly by an ordered pair in ( Word U X. ZZ ); P is the
  arbitrary source function m1 from V to those records, and Q is the
  instantiated function agg measure_closure from Word U to W.

  SetMM words over U are exactly arbitrary finite zero-based source lists.
  NTP4VCNodeModel therefore gives the source concatenation l ++ d :: r.
  NTP4VCBalance and NTP4VCBuilt expand, respectively, the source AVL height
  bound and the sequence-and-height equations for a reconstructed node.

  The source view datatype is represented by the disjoint tagged set
  NTP4VCView U V W. NTP4VCViewModel is exactly the source match that relates
  a view to a t2 value: the empty case has zero height and empty sequence,
  while the node case retains all five fields and every displayed model,
  aggregate, balance, stored-height, and real-height equation.

  NTP4VCLeftCheck and NTP4VCRightCheck expand the universally quantified
  single- and double-rotation side conditions. NTP4VCLeftConstruct and
  NTP4VCRightConstruct expand the corresponding existential construction
  branches, and NTP4VCResultPost expands the final sequence and height
  guarantee. Each proposition-valued source if is rendered by its equivalent
  guarded disjunction, with all natural, integer, view, and abstract-tree
  quantifiers retaining their full source domains.

  Splitting the typed theorem parameters and five assumptions into scoped
  essential hypotheses is bidirectionally equivalent to the source curried
  theorem. The final $a declaration is Metamath's native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAEmpty NTP4VCANode NTP4VCView
  NTP4VCNodeLeft NTP4VCNodeData NTP4VCNodeRight
  NTP4VCNodeHeight NTP4VCNodeSummary
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCBalance NTP4VCBuilt NTP4VCViewModel
  NTP4VCLeftCheck NTP4VCRightCheck
  NTP4VCLeftConstruct NTP4VCRightConstruct
  NTP4VCResultPost NTP4VCBalanceDf
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
ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-balance-syntax $a wff ( NTP4VCBalance A B C D ) $.
ntp4vc-built-syntax $a wff ( NTP4VCBuilt A B C D E ) $.
ntp4vc-view-model-syntax
  $a wff ( NTP4VCViewModel A B C D E ) $.
ntp4vc-left-check-syntax
  $a wff ( NTP4VCLeftCheck A B C D E F G H ) $.
ntp4vc-right-check-syntax
  $a wff ( NTP4VCRightCheck A B C D E F G H ) $.
ntp4vc-left-construct-syntax
  $a wff ( NTP4VCLeftConstruct A B C D E F G H I ) $.
ntp4vc-right-construct-syntax
  $a wff ( NTP4VCRightConstruct A B C D E F G H I J ) $.
ntp4vc-result-post-syntax
  $a wff ( NTP4VCResultPost A B C D E F ) $.
ntp4vc-balance-df-syntax
  $a wff ( NTP4VCBalanceDf A B C D E F G H I ) $.

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

ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.
ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.

ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-balance-def $a |- (
  ( NTP4VCBalance A B C D )
  <->
  (
    -u D <_ (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    /\
    (
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    ) <_ D
  )
) $.

ntp4vc-built-def $a |- (
  ( NTP4VCBuilt A B C D E )
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
    ( NTP4VCHgt ( E ` A ) )
    =
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
  )
) $.

ntp4vc-view-model-def $a |- (
  ( NTP4VCViewModel A B C D E )
  <->
  (
    (
      A = NTP4VCAEmpty
      /\
      (
        ( NTP4VCHgt ( C ` B ) ) = 0
        /\
        ( NTP4VCSeq ( C ` B ) ) = (/)
      )
    )
    \/
    (
      A =/= NTP4VCAEmpty
      /\
      (
        ( NTP4VCSeq ( C ` B ) )
        =
        (
          NTP4VCNodeModel
            ( NTP4VCSeq ( C ` ( NTP4VCNodeLeft A ) ) )
            ( NTP4VCNodeData A )
            ( NTP4VCSeq ( C ` ( NTP4VCNodeRight A ) ) )
        )
        /\
        (
          ( NTP4VCNodeSummary A )
          =
          ( D ` ( NTP4VCSeq ( C ` B ) ) )
          /\
          (
            ( NTP4VCBalance
              ( NTP4VCNodeLeft A )
              ( NTP4VCNodeRight A )
              C E )
            /\
            (
              ( NTP4VCHgt ( C ` B ) ) = ( NTP4VCNodeHeight A )
              /\
              ( NTP4VCNodeHeight A )
              =
              (
                1
                +
                if
                (
                  (
                    NTP4VCHgt ( C ` ( NTP4VCNodeLeft A ) )
                  )
                  <
                  (
                    NTP4VCHgt ( C ` ( NTP4VCNodeRight A ) )
                  ) ,
                  (
                    NTP4VCHgt ( C ` ( NTP4VCNodeRight A ) )
                  ) ,
                  (
                    NTP4VCHgt ( C ` ( NTP4VCNodeLeft A ) )
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

${
  $d h q s x y z A B C D E F G H $.

  ntp4vc-left-check-def $a |- (
    ( NTP4VCLeftCheck A B C D E F G H )
    <->
    A. x e. G
      (
        ( NTP4VCViewModel x A D E F )
        ->
        (
          x =/= NTP4VCAEmpty
          /\
          A. h e. ZZ
            (
              h = ( NTP4VCHgt ( D ` ( NTP4VCNodeRight x ) ) )
              ->
              A. q e. ZZ
                (
                  q = ( NTP4VCHgt ( D ` ( NTP4VCNodeLeft x ) ) )
                  ->
                  (
                    (
                      h <_ q
                      /\
                      (
                        ( NTP4VCBalance
                          ( NTP4VCNodeRight x ) B D F )
                        /\
                        A. y e. H
                          (
                            ( NTP4VCBuilt
                              y ( NTP4VCNodeRight x ) C B D )
                            ->
                            ( NTP4VCBalance
                              ( NTP4VCNodeLeft x ) y D F )
                          )
                      )
                    )
                    \/
                    (
                      -. h <_ q
                      /\
                      A. y e. G
                        (
                          ( NTP4VCViewModel
                            y ( NTP4VCNodeRight x ) D E F )
                          ->
                          (
                            y =/= NTP4VCAEmpty
                            /\
                            (
                              ( NTP4VCBalance
                                ( NTP4VCNodeRight y ) B D F )
                              /\
                              A. z e. H
                                (
                                  ( NTP4VCBuilt
                                    z
                                    ( NTP4VCNodeRight y )
                                    C B D )
                                  ->
                                  (
                                    ( NTP4VCBalance
                                      ( NTP4VCNodeLeft x )
                                      ( NTP4VCNodeLeft y )
                                      D F )
                                    /\
                                    A. s e. H
                                      (
                                        ( NTP4VCBuilt
                                          s
                                          ( NTP4VCNodeLeft x )
                                          ( NTP4VCNodeData x )
                                          ( NTP4VCNodeLeft y )
                                          D )
                                        ->
                                        ( NTP4VCBalance s z D F )
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
  $d h q s x y z A B C D E F G H $.

  ntp4vc-right-check-def $a |- (
    ( NTP4VCRightCheck A B C D E F G H )
    <->
    A. x e. G
      (
        ( NTP4VCViewModel x B D E F )
        ->
        (
          x =/= NTP4VCAEmpty
          /\
          A. h e. ZZ
            (
              h = ( NTP4VCHgt ( D ` ( NTP4VCNodeLeft x ) ) )
              ->
              A. q e. ZZ
                (
                  q = ( NTP4VCHgt ( D ` ( NTP4VCNodeRight x ) ) )
                  ->
                  (
                    (
                      h <_ q
                      /\
                      (
                        ( NTP4VCBalance
                          A ( NTP4VCNodeLeft x ) D F )
                        /\
                        A. y e. H
                          (
                            ( NTP4VCBuilt
                              y A C ( NTP4VCNodeLeft x ) D )
                            ->
                            ( NTP4VCBalance
                              y ( NTP4VCNodeRight x ) D F )
                          )
                      )
                    )
                    \/
                    (
                      -. h <_ q
                      /\
                      A. y e. G
                        (
                          ( NTP4VCViewModel
                            y ( NTP4VCNodeLeft x ) D E F )
                          ->
                          (
                            y =/= NTP4VCAEmpty
                            /\
                            (
                              ( NTP4VCBalance
                                ( NTP4VCNodeRight y )
                                ( NTP4VCNodeRight x )
                                D F )
                              /\
                              A. z e. H
                                (
                                  ( NTP4VCBuilt
                                    z
                                    ( NTP4VCNodeRight y )
                                    ( NTP4VCNodeData x )
                                    ( NTP4VCNodeRight x )
                                    D )
                                  ->
                                  (
                                    ( NTP4VCBalance
                                      A ( NTP4VCNodeLeft y ) D F )
                                    /\
                                    A. s e. H
                                      (
                                        ( NTP4VCBuilt
                                          s A C
                                          ( NTP4VCNodeLeft y ) D )
                                        ->
                                        ( NTP4VCBalance s z D F )
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
  $d h q s x y z A B C D E F G H I $.

  ntp4vc-left-construct-def $a |- (
    ( NTP4VCLeftConstruct A B C D E F G H I )
    <->
    E. x e. H
      (
        ( NTP4VCViewModel x B E F G )
        /\
        (
          x =/= NTP4VCAEmpty
          /\
          E. h e. ZZ
            (
              h = ( NTP4VCHgt ( E ` ( NTP4VCNodeRight x ) ) )
              /\
              E. q e. ZZ
                (
                  q = ( NTP4VCHgt ( E ` ( NTP4VCNodeLeft x ) ) )
                  /\
                  (
                    (
                      h <_ q
                      /\
                      E. y e. I
                        (
                          ( NTP4VCBuilt
                            y ( NTP4VCNodeRight x ) D C E )
                          /\
                          ( NTP4VCBuilt
                            A
                            ( NTP4VCNodeLeft x )
                            ( NTP4VCNodeData x )
                            y E )
                        )
                    )
                    \/
                    (
                      -. h <_ q
                      /\
                      E. y e. H
                        (
                          ( NTP4VCViewModel
                            y ( NTP4VCNodeRight x ) E F G )
                          /\
                          (
                            y =/= NTP4VCAEmpty
                            /\
                            E. z e. I
                              (
                                ( NTP4VCBuilt
                                  z
                                  ( NTP4VCNodeRight y )
                                  D C E )
                                /\
                                E. s e. I
                                  (
                                    ( NTP4VCBuilt
                                      s
                                      ( NTP4VCNodeLeft x )
                                      ( NTP4VCNodeData x )
                                      ( NTP4VCNodeLeft y )
                                      E )
                                    /\
                                    ( NTP4VCBuilt
                                      A s
                                      ( NTP4VCNodeData y )
                                      z E )
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
  $d h q s x y z A B C D E F G H I J $.

  ntp4vc-right-construct-def $a |- (
    ( NTP4VCRightConstruct A B C D E F G H I J )
    <->
    E. h e. ZZ
      (
        h = -u H
        /\
        (
          (
            B < h
            /\
            E. x e. I
              (
                ( NTP4VCViewModel x D F G H )
                /\
                (
                  x =/= NTP4VCAEmpty
                  /\
                  E. q e. ZZ
                    (
                      q =
                      ( NTP4VCHgt ( F ` ( NTP4VCNodeLeft x ) ) )
                      /\
                      E. s e. ZZ
                        (
                          s =
                          ( NTP4VCHgt
                            ( F ` ( NTP4VCNodeRight x ) ) )
                          /\
                          (
                            (
                              q <_ s
                              /\
                              E. y e. J
                                (
                                  ( NTP4VCBuilt
                                    y C E
                                    ( NTP4VCNodeLeft x ) F )
                                  /\
                                  ( NTP4VCBuilt
                                    A y
                                    ( NTP4VCNodeData x )
                                    ( NTP4VCNodeRight x ) F )
                                )
                            )
                            \/
                            (
                              -. q <_ s
                              /\
                              E. y e. I
                                (
                                  ( NTP4VCViewModel
                                    y
                                    ( NTP4VCNodeLeft x )
                                    F G H )
                                  /\
                                  (
                                    y =/= NTP4VCAEmpty
                                    /\
                                    E. z e. J
                                      (
                                        ( NTP4VCBuilt
                                          z
                                          ( NTP4VCNodeRight y )
                                          ( NTP4VCNodeData x )
                                          ( NTP4VCNodeRight x )
                                          F )
                                        /\
                                        E. q e. J
                                          (
                                            ( NTP4VCBuilt
                                              q C E
                                              ( NTP4VCNodeLeft y )
                                              F )
                                            /\
                                            ( NTP4VCBuilt
                                              A q
                                              ( NTP4VCNodeData y )
                                              z F )
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
          \/
          (
            -. B < h
            /\
            ( NTP4VCBuilt A C E D F )
          )
        )
      )
  ) $.
$}

ntp4vc-result-post-def $a |- (
  ( NTP4VCResultPost A B C D E F )
  <->
  (
    ( NTP4VCSeq ( E ` A ) )
    =
    (
      NTP4VCNodeModel
        ( NTP4VCSeq ( E ` B ) )
        D
        ( NTP4VCSeq ( E ` C ) )
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
              ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` C ) ) ,
              ( NTP4VCHgt ( E ` C ) ) ,
              ( NTP4VCHgt ( E ` B ) )
            )
          )
          -
          ( NTP4VCHgt ( E ` A ) )
        )
        /\
        (
          (
            1
            +
            if
            (
              ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` C ) ) ,
              ( NTP4VCHgt ( E ` C ) ) ,
              ( NTP4VCHgt ( E ` B ) )
            )
          )
          -
          ( NTP4VCHgt ( E ` A ) )
        )
        <_ 1
      )
      /\
      (
        ( NTP4VCBalance B C E F )
        ->
        (
          1
          +
          if
          (
            ( NTP4VCHgt ( E ` B ) ) < ( NTP4VCHgt ( E ` C ) ) ,
            ( NTP4VCHgt ( E ` C ) ) ,
            ( NTP4VCHgt ( E ` B ) )
          )
        )
        =
        ( NTP4VCHgt ( E ` A ) )
      )
    )
  )
) $.

${
  $d h x A B C D E F G H I $.

  ntp4vc-balance-df-def $a |- (
    ( NTP4VCBalanceDf A B C D E F G H I )
    <->
    (
      (
        (
          G < A
          /\
          ( NTP4VCLeftCheck B C D E F G H I )
        )
        \/
        (
          -. G < A
          /\
          A. h e. ZZ
            (
              h = -u G
              ->
              (
                (
                  A < h
                  /\
                  ( NTP4VCRightCheck B C D E F G H I )
                )
                \/
                (
                  -. A < h
                  /\
                  ( NTP4VCBalance B C E G )
                )
              )
            )
        )
      )
      /\
      A. x e. I
        (
          (
            (
              G < A
              /\
              ( NTP4VCLeftConstruct x B C D E F G H I )
            )
            \/
            (
              -. G < A
              /\
              ( NTP4VCRightConstruct x A B C D E F G H I )
            )
          )
          ->
          ( NTP4VCResultPost x B C D E G )
        )
    )
  ) $.
$}

${
  $d d e h l m q r s u v w x y z
     A B C D E F G H I J K L M N O P Q U V W X $.

  $( Source carriers and the exact tagged finite-tree datatype. $)
  ntp4vc-t1-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-t2-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-t-carrier-nonempty $e |- W =/= (/) $.
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
  ntp4vc-balancing-positive-natural $e |- E e. NN $.

  $( Source theorem parameters A=hl, B=hr, C=o1, D=l, J=r, and K=d. $)
  ntp4vc-hl-integer $e |- A e. ZZ $.
  ntp4vc-hr-integer $e |- B e. ZZ $.
  ntp4vc-o1-integer $e |- C e. ZZ $.
  ntp4vc-l-type $e |- D e. V $.
  ntp4vc-r-type $e |- J e. V $.
  ntp4vc-d-type $e |- K e. U $.

  ntp4vc-fact0 $e |- (
    ( -u E - 1 )
    <_
    (
      ( NTP4VCHgt ( P ` D ) )
      -
      ( NTP4VCHgt ( P ` J ) )
    )
  ) $.

  ntp4vc-fact1 $e |- (
    (
      ( NTP4VCHgt ( P ` D ) )
      -
      ( NTP4VCHgt ( P ` J ) )
    )
    <_
    ( E + 1 )
  ) $.

  ntp4vc-fact2 $e |- A = ( NTP4VCHgt ( P ` D ) ) $.
  ntp4vc-fact3 $e |- B = ( NTP4VCHgt ( P ` J ) ) $.
  ntp4vc-fact4 $e |- C = -u B $.

  ntp4vc-pearl-avl-balance-vc $a |- (
    C <_ ( A - B )
    /\
    (
      ( A - B ) <_ A
      /\
      A. x e. ZZ
        (
          x = ( A - B )
          ->
          (
            NTP4VCBalanceDf
              x D J K P Q E
              ( NTP4VCView U V W ) V
          )
        )
    )
  ) $.
$}
