$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/avl_AVL_consqtvc: the AVL cons verification condition states
  the sequence, height-growth, and balance obligations for inserting an
  abstract element into an empty or nonempty AVL tree view. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For the arbitrary source type parameter, U, V, and W are respectively the
  instantiated carriers t1 alpha, t2 alpha, and t. A source m alpha record is
  represented exactly by an ordered pair in ( Word U X. ZZ ); P is the
  arbitrary source function m1 from V to those records, and Q is the
  instantiated function agg measure_closure from Word U to W.

  SetMM words over U are exactly arbitrary finite zero-based source lists.
  NTP4VCNodeModel therefore gives the source concatenation l ++ d :: r, and
  NTP4VCInsertStep gives exactly the source sequence equation and the two
  integer height-growth bounds for a recursively constructed tree.

  The source view datatype is represented by the disjoint tagged encoding
  NTP4VCAEmpty and NTP4VCANode. Its five node fields are recovered by the
  explicit projections below. NTP4VCBalance, NTP4VCExtendedBalance,
  NTP4VCRebuildHeight, and NTP4VCNodeResult expand the source balance bound,
  the widened recursive bound, the let-bound reconstructed height condition,
  and the existential nonempty-view result branch.

  Each source match is rendered by its equivalent guarded disjunction. The
  source let expressions are expanded by substitution, and all abstract-tree,
  word, natural, and integer domains retain their full source ranges.
  Splitting the typed theorem parameters and fact0 into scoped essential
  hypotheses is bidirectionally equivalent to the source curried theorem.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCAEmpty NTP4VCANode
  NTP4VCNodeLeft NTP4VCNodeData NTP4VCNodeRight
  NTP4VCNodeHeight NTP4VCNodeSummary
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCBalance NTP4VCInsertStep NTP4VCExtendedBalance
  NTP4VCRebuildHeight NTP4VCNodeResult
$.

ntp4vc-aempty-syntax $a class NTP4VCAEmpty $.
ntp4vc-anode-syntax $a class ( NTP4VCANode A B C D E ) $.
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
ntp4vc-insert-step-syntax
  $a wff ( NTP4VCInsertStep A B C D ) $.
ntp4vc-extended-balance-syntax
  $a wff ( NTP4VCExtendedBalance A B C D ) $.
ntp4vc-rebuild-height-syntax
  $a wff ( NTP4VCRebuildHeight A B C D E ) $.
ntp4vc-node-result-syntax
  $a wff ( NTP4VCNodeResult A B C D E F ) $.

ntp4vc-aempty-def $a |- NTP4VCAEmpty = (/) $.

ntp4vc-anode-def $a |- ( NTP4VCANode A B C D E ) =
  <. 1 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

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

ntp4vc-insert-step-def $a |- (
  ( NTP4VCInsertStep A B C D )
  <->
  (
    ( NTP4VCSeq ( D ` A ) )
    =
    (
      <" B ">
      ++
      ( NTP4VCSeq ( D ` C ) )
    )
    /\
    (
      (
        ( NTP4VCHgt ( D ` A ) )
        -
        ( NTP4VCHgt ( D ` C ) )
      )
      <_
      1
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

ntp4vc-rebuild-height-def $a |- (
  ( NTP4VCRebuildHeight A B C D E )
  <->
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
            ( NTP4VCHgt ( D ` B ) ) < ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` C ) ) ,
            ( NTP4VCHgt ( D ` B ) )
          )
        )
        -
        ( NTP4VCHgt ( D ` A ) )
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
      )
    )
    /\
    (
      ( NTP4VCBalance B C D E )
      ->
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
      =
      ( NTP4VCHgt ( D ` A ) )
    )
  )
) $.

${
  $d x A B C D E F $.

  ntp4vc-node-result-def $a |- (
    ( NTP4VCNodeResult A B C D E F )
    <->
    E. x e. F
      (
        ( NTP4VCInsertStep x C ( NTP4VCNodeLeft B ) D )
        /\
        (
          ( NTP4VCSeq ( D ` A ) )
          =
          (
            NTP4VCNodeModel
              ( NTP4VCSeq ( D ` x ) )
              ( NTP4VCNodeData B )
              ( NTP4VCSeq ( D ` ( NTP4VCNodeRight B ) ) )
          )
          /\
          (
            NTP4VCRebuildHeight
              A x ( NTP4VCNodeRight B ) D E
          )
        )
      )
  ) $.
$}

${
  $d d h l m r s x y z
     A B C E F G H I L M N O P Q U V W X $.

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

  $( Source theorem parameters A=o1, B=t3, and C=d. $)
  ntp4vc-t3-type $e |- B e. V $.
  ntp4vc-d-type $e |- C e. U $.
  ntp4vc-o1-view-type $e |- (
    A = NTP4VCAEmpty
    \/
    E. x e. V
      E. y e. U
        E. z e. V
          E. h e. NN0
            E. s e. W
              A = ( NTP4VCANode x y z h s )
  ) $.

  $( The source fact0 match, with both let-bound heights expanded. $)
  ntp4vc-fact0 $e |- (
    (
      A = NTP4VCAEmpty
      /\
      (
        ( NTP4VCHgt ( P ` B ) ) = 0
        /\
        ( NTP4VCSeq ( P ` B ) ) = (/)
      )
    )
    \/
    (
      A =/= NTP4VCAEmpty
      /\
      (
        ( NTP4VCSeq ( P ` B ) )
        =
        (
          NTP4VCNodeModel
            ( NTP4VCSeq ( P ` ( NTP4VCNodeLeft A ) ) )
            ( NTP4VCNodeData A )
            ( NTP4VCSeq ( P ` ( NTP4VCNodeRight A ) ) )
        )
        /\
        (
          ( NTP4VCNodeSummary A )
          =
          ( Q ` ( NTP4VCSeq ( P ` B ) ) )
          /\
          (
            ( NTP4VCBalance
              ( NTP4VCNodeLeft A )
              ( NTP4VCNodeRight A )
              P E )
            /\
            (
              ( NTP4VCHgt ( P ` B ) ) = ( NTP4VCNodeHeight A )
              /\
              (
                ( NTP4VCNodeHeight A )
                =
                (
                  1
                  +
                  if
                  (
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeLeft A ) )
                    )
                    <
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeRight A ) )
                    ) ,
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeRight A ) )
                    ) ,
                    (
                      NTP4VCHgt ( P ` ( NTP4VCNodeLeft A ) )
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

  ntp4vc-pearl-avl-cons-vc $a |- (
    (
      A = NTP4VCAEmpty
      \/
      (
        A =/= NTP4VCAEmpty
        /\
        (
          (
            0 <_ ( NTP4VCHgt ( P ` B ) )
            /\
            (
              NTP4VCHgt ( P ` ( NTP4VCNodeLeft A ) )
            )
            <
            ( NTP4VCHgt ( P ` B ) )
          )
          /\
          A. x e. V
            (
              (
                NTP4VCInsertStep
                  x C ( NTP4VCNodeLeft A ) P
              )
              ->
              (
                NTP4VCExtendedBalance
                  x ( NTP4VCNodeRight A ) P E
              )
            )
        )
      )
    )
    /\
    A. x e. V
      (
        (
          (
            A = NTP4VCAEmpty
            /\
            (
              ( NTP4VCSeq ( P ` x ) ) = <" C ">
              /\
              ( NTP4VCHgt ( P ` x ) ) = 1
            )
          )
          \/
          (
            A =/= NTP4VCAEmpty
            /\
            ( NTP4VCNodeResult x A C P E V )
          )
        )
        ->
        ( NTP4VCInsertStep x C B P )
      )
  ) $.
$}
