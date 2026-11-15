$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/tables_MapBase_joinqtvc: the AVL-backed finite-map join
  verification condition preserves sorted selection and specifies the
  joined domain, lookup function, cardinality, and one-unit height
  approximation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For an arbitrary inhabited source type alpha, C, D, E, F, and G are the
  carriers t1, t alpha, t3 alpha, t4 alpha, and tree alpha. H is key, I is
  the total preorder le, J is m1, K is repr, L is seq_model, M is
  real_height, N is the balanced subset, O is field, and P is make_func.
  The source m alpha record is represented by an ordered pair in
  ( Word D X. ZZ ).

  SetMM words retain arbitrary finite zero-based source lists.
  NTP4VCEq, NTP4VCLt, selection_possible, and domain expand their source
  definitions with all integer quantifiers and bounds. The unit-valued tree
  summary is omitted from its node encoding because the unit carrier is a
  singleton.

  The source m3 record is expanded definitionally: its domain field is
  NTP4VCDomain by domain_closure_def, its function field is P by
  make_func_closure_def, and its cardinal field is the stored word length.
  Source let bindings are expanded by substitution. Scoped essential
  hypotheses reproduce the source theory and typed theorem parameters.
  All carriers and quantifiers retain their full source domains. The final
  $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCEq NTP4VCLt NTP4VCSelectionPossible
  NTP4VCDomain
$.

ntp4vc-tree-empty-syntax $a class NTP4VCTreeEmpty $.
ntp4vc-tree-node-syntax $a class ( NTP4VCTreeNode A B C D ) $.
ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax $a class ( NTP4VCNodeModel A B C ) $.
ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-lt-syntax $a wff ( NTP4VCLt A B C ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A B C D ) $.
ntp4vc-domain-syntax $a wff ( NTP4VCDomain A B C D ) $.

ntp4vc-tree-empty-def $a |- NTP4VCTreeEmpty = <. 2 , (/) >. $.
ntp4vc-tree-node-def $a |- ( NTP4VCTreeNode A B C D ) =
  <. 3 , <. A , <. B , <. C , D >. >. >. >. $.
ntp4vc-seq-def $a |- ( NTP4VCSeq A ) = ( 1st ` A ) $.
ntp4vc-hgt-def $a |- ( NTP4VCHgt A ) = ( 2nd ` A ) $.
ntp4vc-node-model-def $a |- ( NTP4VCNodeModel A B C ) =
  ( A ++ ( <" B "> ++ C ) ) $.

ntp4vc-eq-def $a |- (
  ( NTP4VCEq A B C )
  <->
  ( <. A , B >. e. C /\ <. B , A >. e. C )
) $.

ntp4vc-lt-def $a |- (
  ( NTP4VCLt A B C )
  <->
  ( <. A , B >. e. C /\ -. <. B , A >. e. C )
) $.

${
  $d i j A B C D $.
  ntp4vc-selection-possible-def $a |- (
    ( NTP4VCSelectionPossible A B C D )
    <->
    A. i e. ZZ A. j e. ZZ
      (
        ( ( 0 <_ i /\ i < j ) /\ j < ( # ` B ) )
        ->
        ( NTP4VCLt ( C ` ( B ` i ) ) ( C ` ( B ` j ) ) D )
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

${
  $d a b d h i j k l o r s u v w x y z
     A B C D E F G H I J K L M N O P Q R $.

  ntp4vc-key-carrier-nonempty $e |- C =/= (/) $.
  ntp4vc-entry-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-t3-carrier-nonempty $e |- E =/= (/) $.
  ntp4vc-t4-carrier-nonempty $e |- F =/= (/) $.

  ntp4vc-key-function $e |- H e. ( C ^m D ) $.
  ntp4vc-le-relation $e |- I C_ ( C X. C ) $.
  ntp4vc-le-reflexive $e |- A. x e. C <. x , x >. e. I $.
  ntp4vc-le-transitive $e |- A. x e. C A. y e. C A. z e. C
    (
      ( <. x , y >. e. I /\ <. y , z >. e. I )
      ->
      <. x , z >. e. I
    ) $.
  ntp4vc-le-total $e |- A. x e. C A. y e. C
    ( <. x , y >. e. I \/ <. y , x >. e. I ) $.

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

  ntp4vc-m1-function $e |- J e. ( ( Word D X. ZZ ) ^m E ) $.
  ntp4vc-repr-function $e |- K e. ( G ^m E ) $.
  ntp4vc-seq-model-function $e |- L e. ( ( Word D ) ^m G ) $.
  ntp4vc-real-height-function $e |- M e. ( ZZ ^m G ) $.
  ntp4vc-balanced-predicate $e |- N C_ G $.

  ntp4vc-seq-model-empty $e |- ( L ` NTP4VCTreeEmpty ) = (/) $.
  ntp4vc-seq-model-node $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      (
        ( L ` ( NTP4VCTreeNode l d r h ) )
        =
        ( NTP4VCNodeModel ( L ` l ) d ( L ` r ) )
      ) $.
  ntp4vc-real-height-empty $e |- ( M ` NTP4VCTreeEmpty ) = 0 $.
  ntp4vc-real-height-node $e |- A. l e. G A. d e. D
    A. r e. G A. h e. NN0
      (
        ( M ` ( NTP4VCTreeNode l d r h ) )
        =
        ( 1 + if ( ( M ` l ) < ( M ` r ) , ( M ` r ) , ( M ` l ) ) )
      ) $.

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
        (/) ( NTP4VCSeq ( J ` ( O ` x ) ) ) H I
    ) $.
  ntp4vc-field-injective $e |- A. x e. F A. y e. F
    ( ( O ` x ) = ( O ` y ) -> x = y ) $.

  ntp4vc-make-func-function
    $e |- P e. ( D ^m ( ( Word D ) X. C ) ) $.
  ntp4vc-make-func-spec $e |- A. s e. Word D A. k e. C A. i e. ZZ
    (
      (
        (
          NTP4VCSelectionPossible (/) s H I
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

  $( Source theorem parameters A=l, B=d, and R=r. $)
  ntp4vc-l-type $e |- A e. F $.
  ntp4vc-d-type $e |- B e. D $.
  ntp4vc-r-type $e |- R e. F $.

  ntp4vc-fact0 $e |- A. k e. C
    (
      (
        NTP4VCDomain
          ( NTP4VCSeq ( J ` ( O ` A ) ) )
          k H I
      )
      ->
      ( NTP4VCLt k ( H ` B ) I )
    ) $.

  ntp4vc-fact1 $e |- A. k e. C
    (
      (
        NTP4VCDomain
          ( NTP4VCSeq ( J ` ( O ` R ) ) )
          k H I
      )
      ->
      ( NTP4VCLt ( H ` B ) k I )
    ) $.

  ntp4vc-pearl-avl-tables-mapbase-join-vc $a |- A. u e. E
    (
      (
        (
          ( NTP4VCSeq ( J ` u ) )
          =
          (
            NTP4VCNodeModel
              ( NTP4VCSeq ( J ` ( O ` A ) ) )
              B
              ( NTP4VCSeq ( J ` ( O ` R ) ) )
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
                    NTP4VCHgt ( J ` ( O ` A ) )
                  )
                  <
                  (
                    NTP4VCHgt ( J ` ( O ` R ) )
                  ) ,
                  (
                    NTP4VCHgt ( J ` ( O ` R ) )
                  ) ,
                  (
                    NTP4VCHgt ( J ` ( O ` A ) )
                  )
                )
              )
              -
              ( NTP4VCHgt ( J ` u ) )
            )
            /\
            (
              (
                1
                +
                if
                (
                  (
                    NTP4VCHgt ( J ` ( O ` A ) )
                  )
                  <
                  (
                    NTP4VCHgt ( J ` ( O ` R ) )
                  ) ,
                  (
                    NTP4VCHgt ( J ` ( O ` R ) )
                  ) ,
                  (
                    NTP4VCHgt ( J ` ( O ` A ) )
                  )
                )
              )
              -
              ( NTP4VCHgt ( J ` u ) )
              <_
              1
            )
          )
        )
        ->
        (
          (
            NTP4VCSelectionPossible
              (/) ( NTP4VCSeq ( J ` u ) ) H I
          )
          /\
          A. v e. F
            (
              ( O ` v ) = u
              ->
              (
                (
                  A. k e. C
                    (
                      ( NTP4VCLt k ( H ` B ) I )
                      ->
                      (
                        (
                          NTP4VCDomain
                            ( NTP4VCSeq ( J ` ( O ` v ) ) )
                            k H I
                        )
                        <->
                        (
                          NTP4VCDomain
                            ( NTP4VCSeq ( J ` ( O ` A ) ) )
                            k H I
                        )
                      )
                    )
                )
                /\
                (
                  A. k e. C
                    (
                      (
                        ( NTP4VCLt k ( H ` B ) I )
                        /\
                        (
                          NTP4VCDomain
                            ( NTP4VCSeq ( J ` ( O ` v ) ) )
                            k H I
                        )
                      )
                      ->
                      (
                        (
                          P
                          `
                          <.
                            ( NTP4VCSeq ( J ` ( O ` v ) ) ) ,
                            k
                          >.
                        )
                        =
                        (
                          P
                          `
                          <.
                            ( NTP4VCSeq ( J ` ( O ` A ) ) ) ,
                            k
                          >.
                        )
                      )
                    )
                  /\
                  (
                    A. k e. C
                      (
                        ( NTP4VCLt ( H ` B ) k I )
                        ->
                        (
                          (
                            NTP4VCDomain
                              ( NTP4VCSeq ( J ` ( O ` v ) ) )
                              k H I
                          )
                          <->
                          (
                            NTP4VCDomain
                              ( NTP4VCSeq ( J ` ( O ` R ) ) )
                              k H I
                          )
                        )
                      )
                    /\
                    (
                      A. k e. C
                        (
                          (
                            ( NTP4VCLt ( H ` B ) k I )
                            /\
                            (
                              NTP4VCDomain
                                ( NTP4VCSeq ( J ` ( O ` v ) ) )
                                k H I
                            )
                          )
                          ->
                          (
                            (
                              P
                              `
                              <.
                                ( NTP4VCSeq ( J ` ( O ` v ) ) ) ,
                                k
                              >.
                            )
                            =
                            (
                              P
                              `
                              <.
                                ( NTP4VCSeq ( J ` ( O ` R ) ) ) ,
                                k
                              >.
                            )
                          )
                        )
                      /\
                      (
                        A. k e. C
                          (
                            ( NTP4VCEq k ( H ` B ) I )
                            ->
                            (
                              (
                                NTP4VCDomain
                                  ( NTP4VCSeq ( J ` ( O ` v ) ) )
                                  k H I
                              )
                              /\
                              (
                                (
                                  P
                                  `
                                  <.
                                    ( NTP4VCSeq ( J ` ( O ` v ) ) ) ,
                                    k
                                  >.
                                )
                                =
                                B
                              )
                            )
                          )
                        /\
                        (
                          ( # ` ( NTP4VCSeq ( J ` ( O ` v ) ) ) )
                          =
                          (
                            (
                              1
                              +
                              (
                                # ` ( NTP4VCSeq ( J ` ( O ` A ) ) )
                              )
                            )
                            +
                            (
                              # ` ( NTP4VCSeq ( J ` ( O ` R ) ) )
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
