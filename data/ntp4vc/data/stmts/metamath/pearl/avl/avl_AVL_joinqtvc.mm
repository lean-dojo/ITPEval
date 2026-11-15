$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_joinqtvc: the AVL join verification condition states
  the view-case, rotation-side-condition, sequence-reconstruction, balance,
  and height-error obligations for joining two abstract AVL trees around an
  element. This file contains no proof.
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
  NTP4VCBalance, NTP4VCBuilt, and NTP4VCHeightApprox expand the displayed
  balance, exact reconstructed-height, and one-unit height-error conditions.

  The source view datatype is represented by the disjoint tagged set
  NTP4VCView U V W. NTP4VCViewModel is exactly the source match that relates
  a view to a t2 value: the empty case has zero height and empty sequence,
  while the node case retains all five fields and every displayed model,
  aggregate, balance, stored-height, and real-height equation.

  NTP4VCFirstObligation expands the nested universal right-view, natural
  negation-witness, height-difference, and rotation checks. The second
  obligation retains the source's internal existential view, natural, and
  abstract-tree witnesses and every reconstruction branch. Each
  proposition-valued source if and datatype match is rendered by its
  equivalent guarded disjunction, and source let expressions are expanded by
  substitution. All list, view, abstract-tree, natural, integer, universal,
  and existential domains retain their full source ranges.

  Splitting the typed theorem parameters and fact0 into scoped essential
  hypotheses is bidirectionally equivalent to the source curried theorem.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCAEmpty NTP4VCANode NTP4VCView
  NTP4VCNodeLeft NTP4VCNodeData NTP4VCNodeRight
  NTP4VCNodeHeight NTP4VCNodeSummary
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCBalance NTP4VCBuilt NTP4VCViewModel
  NTP4VCHeightApprox NTP4VCRebuiltResult
  NTP4VCPrependResult NTP4VCAppendResult
  NTP4VCLeftCheck NTP4VCRightCheck NTP4VCDfCheck
  NTP4VCFirstObligation
  NTP4VCLeftConstruct NTP4VCRightConstruct
  NTP4VCResultAntecedent NTP4VCSecondObligation
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
ntp4vc-height-approx-syntax
  $a wff ( NTP4VCHeightApprox A B C D E ) $.
ntp4vc-rebuilt-result-syntax
  $a wff ( NTP4VCRebuiltResult A B C D E F ) $.
ntp4vc-prepend-result-syntax
  $a wff ( NTP4VCPrependResult A B C D ) $.
ntp4vc-append-result-syntax
  $a wff ( NTP4VCAppendResult A B C D ) $.
ntp4vc-left-check-syntax
  $a wff ( NTP4VCLeftCheck A B C D E F G H ) $.
ntp4vc-right-check-syntax
  $a wff ( NTP4VCRightCheck A B C D E F G H ) $.
ntp4vc-df-check-syntax
  $a wff ( NTP4VCDfCheck A B C D E F G H I J K L ) $.
ntp4vc-first-obligation-syntax
  $a wff ( NTP4VCFirstObligation A B C D E F G H I ) $.
ntp4vc-left-construct-syntax
  $a wff ( NTP4VCLeftConstruct A B C D E F G ) $.
ntp4vc-right-construct-syntax
  $a wff ( NTP4VCRightConstruct A B C D E F G ) $.
ntp4vc-result-antecedent-syntax
  $a wff ( NTP4VCResultAntecedent A B C D E F G H I J ) $.
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

ntp4vc-balance-def $a |- (
  ( NTP4VCBalance A B C D )
  <->
  (
    -u D
    <_
    (
      ( NTP4VCHgt ( C ` B ) )
      -
      ( NTP4VCHgt ( C ` A ) )
    )
    /\
    (
      ( NTP4VCHgt ( C ` B ) )
      -
      ( NTP4VCHgt ( C ` A ) )
    )
    <_ D
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

ntp4vc-height-approx-def $a |- (
  ( NTP4VCHeightApprox A B C D E )
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
      <_ 1
    )
  )
) $.

ntp4vc-rebuilt-result-def $a |- (
  ( NTP4VCRebuiltResult A B C D E F )
  <->
  (
    ( NTP4VCHeightApprox A B C D E )
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
) $.

ntp4vc-prepend-result-def $a |- (
  ( NTP4VCPrependResult A B C D )
  <->
  (
    ( NTP4VCSeq ( D ` A ) )
    =
    ( <" B "> ++ ( NTP4VCSeq ( D ` C ) ) )
    /\
    (
      (
        ( NTP4VCHgt ( D ` A ) )
        -
        ( NTP4VCHgt ( D ` C ) )
      )
      <_ 1
      /\
      0
      <_
      (
        ( NTP4VCHgt ( D ` A ) )
        -
        ( NTP4VCHgt ( D ` C ) )
      )
    )
  )
) $.

ntp4vc-append-result-def $a |- (
  ( NTP4VCAppendResult A B C D )
  <->
  (
    ( NTP4VCSeq ( D ` A ) )
    =
    ( ( NTP4VCSeq ( D ` B ) ) ++ <" C "> )
    /\
    (
      (
        ( NTP4VCHgt ( D ` A ) )
        -
        ( NTP4VCHgt ( D ` B ) )
      )
      <_ 1
      /\
      0
      <_
      (
        ( NTP4VCHgt ( D ` A ) )
        -
        ( NTP4VCHgt ( D ` B ) )
      )
    )
  )
) $.

${
  $d x A B C D E F G H $.

  ntp4vc-left-check-def $a |- (
    ( NTP4VCLeftCheck A B C D E F G H )
    <->
    (
      0
      <_
      if
      (
        ( NTP4VCHgt ( F ` D ) ) < ( NTP4VCHgt ( F ` C ) ) ,
        ( NTP4VCHgt ( F ` C ) ) - ( NTP4VCHgt ( F ` D ) ) ,
        ( NTP4VCHgt ( F ` D ) ) - ( NTP4VCHgt ( F ` C ) )
      )
      /\
      (
        if
        (
          ( NTP4VCHgt ( F ` D ) ) < ( NTP4VCHgt ( F ` B ) ) ,
          ( NTP4VCHgt ( F ` B ) ) - ( NTP4VCHgt ( F ` D ) ) ,
          ( NTP4VCHgt ( F ` D ) ) - ( NTP4VCHgt ( F ` B ) )
        )
        <
        if
        (
          ( NTP4VCHgt ( F ` D ) ) < ( NTP4VCHgt ( F ` C ) ) ,
          ( NTP4VCHgt ( F ` C ) ) - ( NTP4VCHgt ( F ` D ) ) ,
          ( NTP4VCHgt ( F ` D ) ) - ( NTP4VCHgt ( F ` C ) )
        )
        /\
        A. x e. H
          (
            ( NTP4VCHeightApprox x B E D F )
            ->
            (
              ( -u G - 1 )
              <_
              (
                ( NTP4VCHgt ( F ` A ) )
                -
                ( NTP4VCHgt ( F ` x ) )
              )
              /\
              (
                ( NTP4VCHgt ( F ` A ) )
                -
                ( NTP4VCHgt ( F ` x ) )
              )
              <_ ( G + 1 )
            )
          )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G H $.

  ntp4vc-right-check-def $a |- (
    ( NTP4VCRightCheck A B C D E F G H )
    <->
    (
      0
      <_
      if
      (
        ( NTP4VCHgt ( F ` B ) ) < ( NTP4VCHgt ( F ` A ) ) ,
        ( NTP4VCHgt ( F ` A ) ) - ( NTP4VCHgt ( F ` B ) ) ,
        ( NTP4VCHgt ( F ` B ) ) - ( NTP4VCHgt ( F ` A ) )
      )
      /\
      (
        if
        (
          ( NTP4VCHgt ( F ` D ) ) < ( NTP4VCHgt ( F ` A ) ) ,
          ( NTP4VCHgt ( F ` A ) ) - ( NTP4VCHgt ( F ` D ) ) ,
          ( NTP4VCHgt ( F ` D ) ) - ( NTP4VCHgt ( F ` A ) )
        )
        <
        if
        (
          ( NTP4VCHgt ( F ` B ) ) < ( NTP4VCHgt ( F ` A ) ) ,
          ( NTP4VCHgt ( F ` A ) ) - ( NTP4VCHgt ( F ` B ) ) ,
          ( NTP4VCHgt ( F ` B ) ) - ( NTP4VCHgt ( F ` A ) )
        )
        /\
        A. x e. H
          (
            ( NTP4VCHeightApprox x A C D F )
            ->
            (
              ( -u G - 1 )
              <_
              (
                ( NTP4VCHgt ( F ` x ) )
                -
                ( NTP4VCHgt ( F ` E ) )
              )
              /\
              (
                ( NTP4VCHgt ( F ` x ) )
                -
                ( NTP4VCHgt ( F ` E ) )
              )
              <_ ( G + 1 )
            )
          )
      )
    )
  ) $.
$}

${
  $d x y A B C D E F G H I J K L $.

  ntp4vc-df-check-def $a |- (
    ( NTP4VCDfCheck A B C D E F G H I J K L )
    <->
    A. x e. ZZ
      (
        x = ( A - B )
        ->
        (
          (
            K < x
            /\
            ( NTP4VCLeftCheck C D E F G J K L )
          )
          \/
          (
            -. K < x
            /\
            A. y e. ZZ
              (
                y = -u K
                ->
                (
                  (
                    x < y
                    /\
                    ( NTP4VCRightCheck E F G H I J K L )
                  )
                  \/
                  (
                    -. x < y
                    /\
                    ( NTP4VCBalance E F J K )
                  )
                )
              )
          )
        )
      )
  ) $.
$}

${
  $d x y A B C D E F G H I $.

  ntp4vc-first-obligation-def $a |- (
    ( NTP4VCFirstObligation A B C D E F G H I )
    <->
    (
      A = NTP4VCAEmpty
      \/
      (
        A =/= NTP4VCAEmpty
        /\
        A. x e. H
          (
            ( NTP4VCViewModel x C E F G )
            ->
            (
              x = NTP4VCAEmpty
              \/
              (
                x =/= NTP4VCAEmpty
                /\
                A. y e. ZZ
                  (
                    y = -u ( NTP4VCNodeHeight x )
                    ->
                    (
                      (
                        y
                        <_
                        (
                          ( NTP4VCNodeHeight A )
                          -
                          ( NTP4VCNodeHeight x )
                        )
                        /\
                        (
                          ( NTP4VCNodeHeight A )
                          -
                          ( NTP4VCNodeHeight x )
                        )
                        <_ ( NTP4VCNodeHeight A )
                      )
                      /\
                      (
                        NTP4VCDfCheck
                          ( NTP4VCNodeHeight A )
                          ( NTP4VCNodeHeight x )
                          ( NTP4VCNodeLeft A )
                          ( NTP4VCNodeRight A )
                          B C D
                          ( NTP4VCNodeLeft x )
                          ( NTP4VCNodeRight x )
                          E G I
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
  $d x A B C D E F G $.

  ntp4vc-left-construct-def $a |- (
    ( NTP4VCLeftConstruct A B C D E F G )
    <->
    E. x e. G
      (
        ( NTP4VCHeightApprox
          x ( NTP4VCNodeRight B ) D C E )
        /\
        ( NTP4VCRebuiltResult
          A ( NTP4VCNodeLeft B ) ( NTP4VCNodeData B ) x E F )
      )
  ) $.
$}

${
  $d x A B C D E F G $.

  ntp4vc-right-construct-def $a |- (
    ( NTP4VCRightConstruct A B C D E F G )
    <->
    E. x e. G
      (
        ( NTP4VCHeightApprox
          x C D ( NTP4VCNodeLeft B ) E )
        /\
        ( NTP4VCRebuiltResult
          A x ( NTP4VCNodeData B ) ( NTP4VCNodeRight B ) E F )
      )
  ) $.
$}

${
  $d h x y z A B C D E F G H I J $.

  ntp4vc-result-antecedent-def $a |- (
    ( NTP4VCResultAntecedent A B C D E F G H I J )
    <->
    (
      (
        B = NTP4VCAEmpty
        /\
        ( NTP4VCPrependResult A E D F )
      )
      \/
      (
        B =/= NTP4VCAEmpty
        /\
        E. x e. I
          (
            ( NTP4VCViewModel x D F G H )
            /\
            (
              (
                x = NTP4VCAEmpty
                /\
                ( NTP4VCAppendResult A C E F )
              )
              \/
              (
                x =/= NTP4VCAEmpty
                /\
                E. y e. ZZ
                  (
                    y = -u ( NTP4VCNodeHeight x )
                    /\
                    E. z e. ZZ
                      (
                        z =
                        (
                          ( NTP4VCNodeHeight B )
                          -
                          ( NTP4VCNodeHeight x )
                        )
                        /\
                        (
                          (
                            H < z
                            /\
                            ( NTP4VCLeftConstruct A B D E F H J )
                          )
                          \/
                          (
                            -. H < z
                            /\
                            E. h e. ZZ
                              (
                                h = -u H
                                /\
                                (
                                  (
                                    z < h
                                    /\
                                    (
                                      NTP4VCRightConstruct
                                        A x C E F H J
                                    )
                                  )
                                  \/
                                  (
                                    -. z < h
                                    /\
                                    ( NTP4VCBuilt A C E D F )
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
        ( NTP4VCHeightApprox x B D C E )
      )
  ) $.
$}

${
  $d d e h l m q r s u v w x y z
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

  $( Source theorem parameters A=o1, B=l, C=r, and D=d. $)
  ntp4vc-o1-view-type $e |- A e. ( NTP4VCView U V W ) $.
  ntp4vc-l-type $e |- B e. V $.
  ntp4vc-r-type $e |- C e. V $.
  ntp4vc-d-type $e |- D e. U $.

  ntp4vc-fact0 $e |- ( NTP4VCViewModel A B P Q E ) $.

  ntp4vc-pearl-avl-join-vc $a |- (
    (
      NTP4VCFirstObligation
        A B C D P Q E
        ( NTP4VCView U V W ) V
    )
    /\
    (
      NTP4VCSecondObligation
        A B C D P Q E
        ( NTP4VCView U V W ) V
    )
  ) $.
$}
