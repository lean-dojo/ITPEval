$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_fuseqtvc: the AVL fuse verification condition states
  the view-case, balance-bound, sequence-concatenation, and height-loss
  obligations for fusing two abstract AVL trees. This file contains no proof.
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
  NTP4VCNodeHeightValue, NTP4VCHeightLoss, NTP4VCBalance, and
  NTP4VCExtendedBalance directly expand the displayed integer height
  expressions and bounds.

  The source view datatype is represented by the disjoint tagged set
  NTP4VCView U V W. NTP4VCViewModel is exactly the source match that relates
  a view to a t2 value: the empty case has zero height and empty sequence,
  while the node case retains all five fields and every displayed model,
  aggregate, balance, stored-height, and real-height equation.

  NTP4VCFirstObligation expands the universally quantified right-view
  analysis and its internal d0 and r' quantifiers.
  NTP4VCResultAntecedent preserves the internal existential o2, d2, and res
  witnesses of the result branch, while NTP4VCResultPost and
  NTP4VCSecondObligation expand the final sequence and height guarantee.
  Each source pattern match is rendered by its equivalent equality-guarded
  disjunction, with all abstract, view, natural, integer, list, universal, and
  existential domains unchanged.

  Splitting the typed theorem parameters and three assumptions into scoped
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
  NTP4VCNodeHeightValue NTP4VCHeightLoss
  NTP4VCBalance NTP4VCExtendedBalance NTP4VCViewModel
  NTP4VCFirstObligation NTP4VCResultAntecedent
  NTP4VCResultPost NTP4VCSecondObligation
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
ntp4vc-node-height-value-syntax
  $a class ( NTP4VCNodeHeightValue A B C ) $.

ntp4vc-height-loss-syntax
  $a wff ( NTP4VCHeightLoss A B C D ) $.
ntp4vc-balance-syntax $a wff ( NTP4VCBalance A B C D ) $.
ntp4vc-extended-balance-syntax
  $a wff ( NTP4VCExtendedBalance A B C D ) $.
ntp4vc-view-model-syntax
  $a wff ( NTP4VCViewModel A B C D E ) $.
ntp4vc-first-obligation-syntax
  $a wff ( NTP4VCFirstObligation A B C D E F G H I ) $.
ntp4vc-result-antecedent-syntax
  $a wff ( NTP4VCResultAntecedent A B C D E F G H I J ) $.
ntp4vc-result-post-syntax
  $a wff ( NTP4VCResultPost A B C D ) $.
ntp4vc-second-obligation-syntax
  $a wff ( NTP4VCSecondObligation A B C D E F G H I ) $.

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

ntp4vc-node-height-value-def $a |- (
  NTP4VCNodeHeightValue A B C
) =
(
  1
  +
  if
  (
    ( NTP4VCHgt ( C ` A ) ) < ( NTP4VCHgt ( C ` B ) ) ,
    ( NTP4VCHgt ( C ` B ) ) ,
    ( NTP4VCHgt ( C ` A ) )
  )
) $.

ntp4vc-height-loss-def $a |- (
  ( NTP4VCHeightLoss A B C D )
  <->
  (
    0
    <_
    (
      ( NTP4VCNodeHeightValue A B D )
      -
      ( NTP4VCHgt ( D ` C ) )
    )
    /\
    (
      ( NTP4VCNodeHeightValue A B D )
      -
      ( NTP4VCHgt ( D ` C ) )
    )
    <_ 1
  )
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
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    <_ D
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
      ( NTP4VCHgt ( C ` A ) )
      -
      ( NTP4VCHgt ( C ` B ) )
    )
    <_ ( D + 1 )
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
                NTP4VCNodeHeightValue
                  ( NTP4VCNodeLeft A )
                  ( NTP4VCNodeRight A )
                  C
              )
            )
          )
        )
      )
    )
  )
) $.

${
  $d x y z A B C D E F G H I $.

  ntp4vc-first-obligation-def $a |- (
    ( NTP4VCFirstObligation A B C D E F G H I )
    <->
    (
      A = NTP4VCAEmpty
      \/
      (
        A =/= NTP4VCAEmpty
        /\
        A. x e. G
          (
            ( NTP4VCViewModel x C D E F )
            ->
            (
              x = NTP4VCAEmpty
              \/
              (
                x =/= NTP4VCAEmpty
                /\
                (
                  ( NTP4VCBalance
                    ( NTP4VCNodeLeft x )
                    ( NTP4VCNodeRight x )
                    D F )
                  /\
                  A. y e. H
                    A. z e. I
                      (
                        (
                          (
                            NTP4VCNodeModel
                              ( NTP4VCSeq
                                ( D ` ( NTP4VCNodeLeft x ) ) )
                              ( NTP4VCNodeData x )
                              ( NTP4VCSeq
                                ( D ` ( NTP4VCNodeRight x ) ) )
                          )
                          =
                          (
                            <" y ">
                            ++
                            ( NTP4VCSeq ( D ` z ) )
                          )
                          /\
                          ( NTP4VCHeightLoss
                            ( NTP4VCNodeLeft x )
                            ( NTP4VCNodeRight x )
                            z D )
                        )
                        ->
                        ( NTP4VCExtendedBalance B z D F )
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
  $d x y z A B C D E F G H I J $.

  ntp4vc-result-antecedent-def $a |- (
    ( NTP4VCResultAntecedent A B C D E F G H I J )
    <->
    (
      (
        B = NTP4VCAEmpty
        /\
        A = D
      )
      \/
      (
        B =/= NTP4VCAEmpty
        /\
        E. x e. H
          (
            ( NTP4VCViewModel x D E F G )
            /\
            (
              (
                x = NTP4VCAEmpty
                /\
                A = C
              )
              \/
              (
                x =/= NTP4VCAEmpty
                /\
                E. y e. I
                  E. z e. J
                    (
                      (
                        (
                          (
                            NTP4VCNodeModel
                              ( NTP4VCSeq
                                ( E ` ( NTP4VCNodeLeft x ) ) )
                              ( NTP4VCNodeData x )
                              ( NTP4VCSeq
                                ( E ` ( NTP4VCNodeRight x ) ) )
                          )
                          =
                          (
                            <" y ">
                            ++
                            ( NTP4VCSeq ( E ` z ) )
                          )
                          /\
                          ( NTP4VCHeightLoss
                            ( NTP4VCNodeLeft x )
                            ( NTP4VCNodeRight x )
                            z E )
                        )
                        /\
                        (
                          ( NTP4VCSeq ( E ` A ) )
                          =
                          (
                            NTP4VCNodeModel
                              ( NTP4VCSeq ( E ` C ) )
                              y
                              ( NTP4VCSeq ( E ` z ) )
                          )
                          /\
                          (
                            ( NTP4VCHeightLoss C z A E )
                            /\
                            (
                              ( NTP4VCBalance C z E G )
                              ->
                              (
                                NTP4VCNodeHeightValue C z E
                              )
                              =
                              ( NTP4VCHgt ( E ` A ) )
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

ntp4vc-result-post-def $a |- (
  ( NTP4VCResultPost A B C D )
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
        ( NTP4VCNodeHeightValue B C D )
        -
        ( NTP4VCHgt ( D ` A ) )
      )
      <_ 1
      /\
      0
      <_
      (
        ( NTP4VCNodeHeightValue B C D )
        -
        ( NTP4VCHgt ( D ` A ) )
      )
    )
  )
) $.

${
  $d x A B C D E F G H I $.

  ntp4vc-second-obligation-def $a |- (
    ( NTP4VCSecondObligation A B C D E F G H I )
    <->
    A. x e. I
      (
        (
          NTP4VCResultAntecedent
            x A B C D E F G H I
        )
        ->
        ( NTP4VCResultPost x B C D )
      )
  ) $.
$}

${
  $d d h l m q r s x y z
     A B C D E F G H I J L M N O P Q U V W X $.

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
  ntp4vc-seq-model-empty $e |- ( M ` NTP4VCTreeEmpty ) = (/) $.
  ntp4vc-seq-model-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      ( M ` ( NTP4VCTreeNode l d r h m ) )
      =
      ( NTP4VCNodeModel ( M ` l ) d ( M ` r ) ) $.
  ntp4vc-real-height-empty $e |- ( N ` NTP4VCTreeEmpty ) = 0 $.
  ntp4vc-real-height-node $e |- A. l e. X A. d e. U
    A. r e. X A. h e. NN0 A. m e. W
      ( N ` ( NTP4VCTreeNode l d r h m ) )
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
    ( G ` <. x , ( G ` <. y , z >. ) >. )
    =
    ( G ` <. ( G ` <. x , y >. ) , z >. ) $.
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

  $( Source theorem parameters A=l, B=r, and C=o1. $)
  ntp4vc-l-type $e |- A e. V $.
  ntp4vc-r-type $e |- B e. V $.
  ntp4vc-o1-view-type $e |- C e. ( NTP4VCView U V W ) $.

  ntp4vc-fact0 $e |- (
    -u E
    <_
    (
      ( NTP4VCHgt ( P ` A ) )
      -
      ( NTP4VCHgt ( P ` B ) )
    )
  ) $.

  ntp4vc-fact1 $e |- (
    (
      ( NTP4VCHgt ( P ` A ) )
      -
      ( NTP4VCHgt ( P ` B ) )
    )
    <_ E
  ) $.

  ntp4vc-fact2 $e |- (
    NTP4VCViewModel C A P Q E
  ) $.

  ntp4vc-pearl-avl-fuse-vc $a |- (
    (
      NTP4VCFirstObligation
        C A B P Q E
        ( NTP4VCView U V W ) U V
    )
    /\
    (
      NTP4VCSecondObligation
        C A B P Q E
        ( NTP4VCView U V W ) U V
    )
  ) $.
$}
