$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/tables_MapBase_viewqtvc: the AVL-backed finite-map view
  verification condition relates an abstract tree view to sorted child maps
  and specifies the resulting map cardinality, domains, and lookup values in
  the empty and node cases. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For an arbitrary inhabited source type alpha, C, D, E, F, and G are the
  instantiated carriers t1, t alpha, t3 alpha, t4 alpha, and tree alpha.
  H is key, I is the total preorder le, J is m1, K is repr, L is seq_model,
  M is real_height, N is the balanced subset, O is field, P is make_func,
  and Q is the positive natural balancing parameter. The source m alpha
  record is represented exactly by an ordered pair in ( Word D X. ZZ ).

  SetMM words are arbitrary finite zero-based lists. The source view and
  result-view datatypes use disjoint tagged encodings that retain every
  abstract-tree, entry, natural-height, and unit field; the unit carrier is
  represented by its unique value 0. NTP4VCEq and NTP4VCLt expand the source
  definitions from le. Selection-possible and domain retain every source
  integer quantifier and bound.

  The m3 record is expanded definitionally: its domn field is the source
  list-domain predicate by domain_closure_def, its func field is P by
  make_func_closure_def, and its card field is the stored word length. The
  let bindings o1, hl, hr, and k0 are expanded by substitution. Each datatype
  match is represented by its exhaustive guarded cases.

  Splitting the source theory and theorem parameters into scoped essential
  hypotheses is bidirectionally equivalent to the curried source statement.
  All carriers and quantifiers retain their full source domains. The final
  $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCViewEmpty NTP4VCViewNode NTP4VCView
  NTP4VCView1Empty NTP4VCView1Node NTP4VCView1
  NTP4VCNodeLeft NTP4VCNodeData NTP4VCNodeRight
  NTP4VCNodeHeight NTP4VCNodeSummary
  NTP4VCView1Left NTP4VCView1Data NTP4VCView1Right
  NTP4VCView1Height
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCEq NTP4VCLt NTP4VCSelectionPossible NTP4VCDomain
  NTP4VCMapCard NTP4VCMapDom NTP4VCMapFunc
  NTP4VCLeftSpec NTP4VCRightSpec NTP4VCPivotSpec
  NTP4VCViewPremise NTP4VCViewAvailability
  NTP4VCResultLink NTP4VCResultPost
$.

ntp4vc-tree-empty-syntax $a class NTP4VCTreeEmpty $.
ntp4vc-tree-node-syntax
  $a class ( NTP4VCTreeNode A B C D ) $.

ntp4vc-view-empty-syntax $a class NTP4VCViewEmpty $.
ntp4vc-view-node-syntax
  $a class ( NTP4VCViewNode A B C D E ) $.
ntp4vc-view-syntax $a class ( NTP4VCView A B ) $.

ntp4vc-view1-empty-syntax $a class NTP4VCView1Empty $.
ntp4vc-view1-node-syntax
  $a class ( NTP4VCView1Node A B C D ) $.
ntp4vc-view1-syntax $a class ( NTP4VCView1 A B ) $.

ntp4vc-node-left-syntax $a class ( NTP4VCNodeLeft A ) $.
ntp4vc-node-data-syntax $a class ( NTP4VCNodeData A ) $.
ntp4vc-node-right-syntax $a class ( NTP4VCNodeRight A ) $.
ntp4vc-node-height-syntax $a class ( NTP4VCNodeHeight A ) $.
ntp4vc-node-summary-syntax $a class ( NTP4VCNodeSummary A ) $.

ntp4vc-view1-left-syntax $a class ( NTP4VCView1Left A ) $.
ntp4vc-view1-data-syntax $a class ( NTP4VCView1Data A ) $.
ntp4vc-view1-right-syntax $a class ( NTP4VCView1Right A ) $.
ntp4vc-view1-height-syntax $a class ( NTP4VCView1Height A ) $.

ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax
  $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-lt-syntax $a wff ( NTP4VCLt A B C ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A B C D ) $.
ntp4vc-domain-syntax
  $a wff ( NTP4VCDomain A B C D ) $.

ntp4vc-map-card-syntax $a class ( NTP4VCMapCard A B C ) $.
ntp4vc-map-dom-syntax
  $a wff ( NTP4VCMapDom A B C D E F ) $.
ntp4vc-map-func-syntax
  $a class ( NTP4VCMapFunc A B C D E ) $.

ntp4vc-left-spec-syntax
  $a wff ( NTP4VCLeftSpec A B C D E F G H I ) $.
ntp4vc-right-spec-syntax
  $a wff ( NTP4VCRightSpec A B C D E F G H I ) $.
ntp4vc-pivot-spec-syntax
  $a wff ( NTP4VCPivotSpec A B C D E F G H I ) $.

ntp4vc-view-premise-syntax
  $a wff ( NTP4VCViewPremise A B C D E ) $.
ntp4vc-view-availability-syntax
  $a wff ( NTP4VCViewAvailability A B C D E F ) $.
ntp4vc-result-link-syntax
  $a wff ( NTP4VCResultLink A B C D ) $.
ntp4vc-result-post-syntax
  $a wff ( NTP4VCResultPost A B C D E F G H I ) $.

ntp4vc-tree-empty-def $a |- NTP4VCTreeEmpty = <. 4 , (/) >. $.

ntp4vc-tree-node-def $a |- ( NTP4VCTreeNode A B C D ) =
  <. 5 , <. A , <. B , <. C , D >. >. >. >. $.

ntp4vc-view-empty-def $a |- NTP4VCViewEmpty = (/) $.

ntp4vc-view-node-def $a |- ( NTP4VCViewNode A B C D E ) =
  <. 1 , <. A , <. B , <. C , <. D , E >. >. >. >. >. $.

${
  $d d h l r s x A B $.

  ntp4vc-view-def $a |- ( NTP4VCView A B ) =
    { x |
      (
        x = NTP4VCViewEmpty
        \/
        E. l e. B
          E. d e. A
            E. r e. B
              E. h e. NN0
                E. s e. { 0 }
                  x = ( NTP4VCViewNode l d r h s )
      )
    } $.
$}

ntp4vc-view1-empty-def $a |- NTP4VCView1Empty = <. 2 , (/) >. $.

ntp4vc-view1-node-def $a |- ( NTP4VCView1Node A B C D ) =
  <. 3 , <. A , <. B , <. C , D >. >. >. >. $.

${
  $d d h l r x A B $.

  ntp4vc-view1-def $a |- ( NTP4VCView1 A B ) =
    { x |
      (
        x = NTP4VCView1Empty
        \/
        E. l e. B
          E. d e. A
            E. r e. B
              E. h e. NN0
                x = ( NTP4VCView1Node l d r h )
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

ntp4vc-view1-left-def $a |- ( NTP4VCView1Left A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-view1-data-def $a |- ( NTP4VCView1Data A ) =
  ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-view1-right-def $a |- ( NTP4VCView1Right A ) =
  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-view1-height-def $a |- ( NTP4VCView1Height A ) =
  ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.
ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.

ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-eq-def $a |- (
  ( NTP4VCEq A B C )
  <->
  (
    <. A , B >. e. C
    /\
    <. B , A >. e. C
  )
) $.

ntp4vc-lt-def $a |- (
  ( NTP4VCLt A B C )
  <->
  (
    <. A , B >. e. C
    /\
    -. <. B , A >. e. C
  )
) $.

${
  $d i j A B C D $.

  ntp4vc-selection-possible-def $a |- (
    ( NTP4VCSelectionPossible A B C D )
    <->
    A. i e. ZZ A. j e. ZZ
      (
        (
          ( 0 <_ i /\ i < j )
          /\
          j < ( # ` B )
        )
        ->
        (
          NTP4VCLt
            ( C ` ( B ` i ) )
            ( C ` ( B ` j ) )
            D
        )
      )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-domain-def $a |- (
    ( NTP4VCDomain A B C D )
    <->
    E. i e. ZZ
      (
        ( 0 <_ i /\ i < ( # ` A ) )
        /\
        ( NTP4VCEq ( C ` ( A ` i ) ) B D )
      )
  ) $.
$}

ntp4vc-map-card-def $a |- ( NTP4VCMapCard A B C ) =
  ( # ` ( NTP4VCSeq ( B ` ( C ` A ) ) ) ) $.

ntp4vc-map-dom-def $a |- (
  ( NTP4VCMapDom A B C D E F )
  <->
  (
    NTP4VCDomain
      ( NTP4VCSeq ( E ` ( F ` A ) ) )
      B C D
  )
) $.

ntp4vc-map-func-def $a |- ( NTP4VCMapFunc A B C D E ) =
  (
    C
    `
    <.
      ( NTP4VCSeq ( D ` ( E ` A ) ) ) ,
      B
    >.
  ) $.

${
  $d k A B C D E F G H I $.

  ntp4vc-left-spec-def $a |- (
    ( NTP4VCLeftSpec A B C D E F G H I )
    <->
    (
      A. k e. D
        (
          ( NTP4VCLt k C F )
          ->
          (
            ( NTP4VCMapDom B k E F G H )
            <->
            ( NTP4VCMapDom A k E F G H )
          )
        )
      /\
      (
        A. k e. D
          (
            (
              ( NTP4VCLt k C F )
              /\
              ( NTP4VCMapDom B k E F G H )
            )
            ->
            (
              ( NTP4VCMapFunc B k I G H )
              =
              ( NTP4VCMapFunc A k I G H )
            )
          )
        /\
        A. k e. D
          (
            <. C , k >. e. F
            ->
            -. ( NTP4VCMapDom B k E F G H )
          )
      )
    )
  ) $.
$}

${
  $d k A B C D E F G H I $.

  ntp4vc-right-spec-def $a |- (
    ( NTP4VCRightSpec A B C D E F G H I )
    <->
    (
      A. k e. D
        (
          ( NTP4VCLt C k F )
          ->
          (
            ( NTP4VCMapDom B k E F G H )
            <->
            ( NTP4VCMapDom A k E F G H )
          )
        )
      /\
      (
        A. k e. D
          (
            (
              ( NTP4VCLt C k F )
              /\
              ( NTP4VCMapDom B k E F G H )
            )
            ->
            (
              ( NTP4VCMapFunc B k I G H )
              =
              ( NTP4VCMapFunc A k I G H )
            )
          )
        /\
        A. k e. D
          (
            <. k , C >. e. F
            ->
            -. ( NTP4VCMapDom B k E F G H )
          )
      )
    )
  ) $.
$}

${
  $d k A B C D E F G H I $.

  ntp4vc-pivot-spec-def $a |- (
    ( NTP4VCPivotSpec A B C D E F G H I )
    <->
    (
      A. k e. D
        (
          ( NTP4VCEq k C F )
          ->
          (
            ( NTP4VCMapDom A k E F G H )
            /\
            ( NTP4VCMapFunc A k I G H ) = B
          )
        )
      /\
      (
        ( NTP4VCMapDom A C E F G H )
        /\
        ( NTP4VCMapFunc A C I G H ) = B
      )
    )
  ) $.
$}

ntp4vc-view-premise-def $a |- (
  ( NTP4VCViewPremise A B C D E )
  <->
  (
    (
      A = NTP4VCViewEmpty
      /\
      (
        ( NTP4VCHgt ( C ` ( D ` B ) ) ) = 0
        /\
        ( NTP4VCSeq ( C ` ( D ` B ) ) ) = (/)
      )
    )
    \/
    (
      A =/= NTP4VCViewEmpty
      /\
      (
        ( NTP4VCSeq ( C ` ( D ` B ) ) )
        =
        (
          NTP4VCNodeModel
            ( NTP4VCSeq ( C ` ( NTP4VCNodeLeft A ) ) )
            ( NTP4VCNodeData A )
            ( NTP4VCSeq ( C ` ( NTP4VCNodeRight A ) ) )
        )
        /\
        (
          ( NTP4VCNodeSummary A ) = 0
          /\
          (
            (
              -u E
              <_
              (
                ( NTP4VCHgt ( C ` ( NTP4VCNodeLeft A ) ) )
                -
                ( NTP4VCHgt ( C ` ( NTP4VCNodeRight A ) ) )
              )
              /\
              (
                (
                  ( NTP4VCHgt ( C ` ( NTP4VCNodeLeft A ) ) )
                  -
                  ( NTP4VCHgt ( C ` ( NTP4VCNodeRight A ) ) )
                )
                <_
                E
              )
            )
            /\
            (
              ( NTP4VCHgt ( C ` ( D ` B ) ) )
              =
              ( NTP4VCNodeHeight A )
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
  )
) $.

${
  $d x A B C D E F $.

  ntp4vc-view-availability-def $a |- (
    ( NTP4VCViewAvailability A B C D E F )
    <->
    (
      A = NTP4VCViewEmpty
      \/
      (
        A =/= NTP4VCViewEmpty
        /\
        (
          (
            NTP4VCSelectionPossible
              0
              ( NTP4VCSeq ( D ` ( NTP4VCNodeRight A ) ) )
              B C
          )
          /\
          A. x e. F
            (
              ( E ` x ) = ( NTP4VCNodeRight A )
              ->
              (
                NTP4VCSelectionPossible
                  0
                  ( NTP4VCSeq ( D ` ( NTP4VCNodeLeft A ) ) )
                  B C
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d x y A B C D $.

  ntp4vc-result-link-def $a |- (
    ( NTP4VCResultLink A B C D )
    <->
    (
      (
        A = NTP4VCViewEmpty
        /\
        B = NTP4VCView1Empty
      )
      \/
      (
        A =/= NTP4VCViewEmpty
        /\
        E. x e. D
          (
            ( C ` x ) = ( NTP4VCNodeRight A )
            /\
            E. y e. D
              (
                ( C ` y ) = ( NTP4VCNodeLeft A )
                /\
                B =
                (
                  NTP4VCView1Node
                    y
                    ( NTP4VCNodeData A )
                    x
                    ( NTP4VCNodeHeight A )
                )
              )
          )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G H I $.

  ntp4vc-result-post-def $a |- (
    ( NTP4VCResultPost A B C D E F G H I )
    <->
    (
      (
        A = NTP4VCView1Empty
        /\
        (
          ( NTP4VCMapCard B G H ) = 0
          /\
          A. x e. C -. ( NTP4VCMapDom B x E F G H )
        )
      )
      \/
      (
        A =/= NTP4VCView1Empty
        /\
        (
          ( NTP4VCMapCard B G H )
          =
          (
            (
              1
              +
              (
                NTP4VCMapCard
                  ( NTP4VCView1Left A ) G H
              )
            )
            +
            (
              NTP4VCMapCard
                ( NTP4VCView1Right A ) G H
            )
          )
          /\
          (
            ( NTP4VCView1Height A )
            =
            ( NTP4VCHgt ( G ` ( H ` B ) ) )
            /\
            (
              (
                NTP4VCLeftSpec
                  B
                  ( NTP4VCView1Left A )
                  ( E ` ( NTP4VCView1Data A ) )
                  C E F G H I
              )
              /\
              (
                (
                  NTP4VCRightSpec
                    B
                    ( NTP4VCView1Right A )
                    ( E ` ( NTP4VCView1Data A ) )
                    C E F G H I
                )
                /\
                (
                  NTP4VCPivotSpec
                    B
                    ( NTP4VCView1Data A )
                    ( E ` ( NTP4VCView1Data A ) )
                    C E F G H I
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
  $d a b d h i j k l o r s u v w x y z
     A B C D E F G H I J K L M N O P Q $.

  ntp4vc-key-carrier-nonempty $e |- C =/= (/) $.
  ntp4vc-entry-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-t3-carrier-nonempty $e |- E =/= (/) $.
  ntp4vc-t4-carrier-nonempty $e |- F =/= (/) $.

  ntp4vc-key-function $e |- H e. ( C ^m D ) $.
  ntp4vc-le-relation $e |- I C_ ( C X. C ) $.
  ntp4vc-le-reflexive $e |- A. x e. C <. x , x >. e. I $.
  ntp4vc-le-transitive $e |- A. x e. C A. y e. C A. z e. C
    (
      (
        <. x , y >. e. I
        /\
        <. y , z >. e. I
      )
      ->
      <. x , z >. e. I
    ) $.
  ntp4vc-le-total $e |- A. x e. C A. y e. C
    (
      <. x , y >. e. I
      \/
      <. y , x >. e. I
    ) $.

  ntp4vc-tree-carrier-nonempty $e |- G =/= (/) $.
  ntp4vc-tree-empty-in-carrier $e |- NTP4VCTreeEmpty e. G $.
  ntp4vc-tree-node-closure $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      ( NTP4VCTreeNode l d r h ) e. G $.
  ntp4vc-tree-exhaustive $e |- A. x e. G
    (
      x = NTP4VCTreeEmpty
      \/
      E. l e. G E. d e. D E. r e. G E. h e. NN0
        x = ( NTP4VCTreeNode l d r h )
    ) $.

  ntp4vc-m1-function
    $e |- J e. ( ( Word D X. ZZ ) ^m E ) $.
  ntp4vc-repr-function $e |- K e. ( G ^m E ) $.
  ntp4vc-seq-model-function $e |- L e. ( ( Word D ) ^m G ) $.
  ntp4vc-real-height-function $e |- M e. ( ZZ ^m G ) $.
  ntp4vc-balanced-predicate $e |- N C_ G $.

  ntp4vc-seq-model-empty $e |- ( L ` NTP4VCTreeEmpty ) = (/) $.
  ntp4vc-seq-model-node $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      (
        L ` ( NTP4VCTreeNode l d r h )
      )
      =
      ( NTP4VCNodeModel ( L ` l ) d ( L ` r ) ) $.
  ntp4vc-real-height-empty $e |- ( M ` NTP4VCTreeEmpty ) = 0 $.
  ntp4vc-real-height-node $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      (
        M ` ( NTP4VCTreeNode l d r h )
      )
      =
      ( 1 + if ( ( M ` l ) < ( M ` r ) , ( M ` r ) , ( M ` l ) ) ) $.

  ntp4vc-balancing-positive-natural $e |- Q e. NN $.
  ntp4vc-balanced-empty $e |- NTP4VCTreeEmpty e. N $.
  ntp4vc-balanced-node $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      (
        ( NTP4VCTreeNode l d r h ) e. N
        <->
        (
          h = ( M ` ( NTP4VCTreeNode l d r h ) )
          /\
          (
            (
              -u Q <_ ( ( M ` r ) - ( M ` l ) )
              /\
              ( ( M ` r ) - ( M ` l ) ) <_ Q
            )
            /\
            ( l e. N /\ r e. N )
          )
        )
      ) $.

  ntp4vc-t3-invariant $e |- A. x e. E
    (
      (
        ( K ` x ) e. N
        /\
        ( NTP4VCSeq ( J ` x ) ) = ( L ` ( K ` x ) )
      )
      /\
      ( NTP4VCHgt ( J ` x ) ) = ( M ` ( K ` x ) )
    ) $.
  ntp4vc-t3-injective $e |- A. x e. E A. y e. E
    (
      (
        ( K ` x ) = ( K ` y )
        /\
        ( J ` x ) = ( J ` y )
      )
      ->
      x = y
    ) $.

  ntp4vc-field-function $e |- O e. ( E ^m F ) $.
  ntp4vc-t4-invariant $e |- A. x e. F
    (
      NTP4VCSelectionPossible
        0 ( NTP4VCSeq ( J ` ( O ` x ) ) ) H I
    ) $.
  ntp4vc-field-injective $e |- A. x e. F A. y e. F
    (
      ( O ` x ) = ( O ` y )
      ->
      x = y
    ) $.

  ntp4vc-make-func-function
    $e |- P e. ( D ^m ( ( Word D ) X. C ) ) $.
  ntp4vc-make-func-spec $e |- A. s e. Word D A. k e. C
    A. i e. ZZ
      (
        (
          (
            NTP4VCSelectionPossible 0 s H I
            /\
            ( NTP4VCDomain s k H I )
          )
          /\
          (
            ( 0 <_ i /\ i < ( # ` s ) )
            /\
            ( NTP4VCEq ( H ` ( s ` i ) ) k I )
          )
        )
        ->
        ( P ` <. s , k >. ) = ( s ` i )
      ) $.

  $( Source theorem parameter A=t5. $)
  ntp4vc-t5-type $e |- A e. F $.

  ntp4vc-pearl-avl-tables-mapbase-view-vc $a |- (
    A. o e. ( NTP4VCView D E )
      (
        ( NTP4VCViewPremise o A J O Q )
        ->
        (
          ( NTP4VCViewAvailability o H I J O F )
          /\
          A. r e. ( NTP4VCView1 D F )
            (
              ( NTP4VCResultLink o r O F )
              ->
              ( NTP4VCResultPost r A C D H I J O P )
            )
        )
      )
  ) $.
$}
