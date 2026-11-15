$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/avl/tables_MapBase_getqtvc: the AVL-backed finite-map get
  verification condition relates a key-selected split of the stored sorted
  sequence to map-domain membership, positive cardinality, and the returned
  key-value entry. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For an arbitrary inhabited source type alpha, C, D, E, F, and G are the
  carriers t1, t alpha, t3 alpha, t4 alpha, and tree alpha. H is key, I is
  the total preorder le, J is m1, K is repr, L is seq_model, M is
  real_height, N is the balanced subset, O is field, and P is make_func.
  The source m alpha record is represented exactly by an ordered pair in
  ( Word D X. ZZ ).

  SetMM words are arbitrary finite zero-based lists. Source options and
  splits use disjoint tagged encodings, and rebuilding directly expands the
  source list definition. NTP4VCEq and NTP4VCLt expand the source definitions
  from le. Selection-possible, selected, and domain retain all source integer
  quantifiers and bounds.

  The m3 record is expanded definitionally: its domain field is domain by
  domain_closure_def, its function field is P by make_func_closure_def, and
  its cardinal field is the stored word length. The let binding o1 is
  expanded by substitution, and each option match is represented by its
  exhaustive tagged cases. Unused inhabited source types and the unit-valued
  tree summary are conservatively represented by singleton carriers.

  Splitting the source theory and theorem parameters into scoped essential
  hypotheses is bidirectionally equivalent to the curried source statement.
  All carriers and quantifiers retain their full source domains. The final
  $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCTreeEmpty NTP4VCTreeNode
  NTP4VCNone NTP4VCSome NTP4VCOption
  NTP4VCSplitMk NTP4VCSplit NTP4VCSplitLeft
  NTP4VCSplitMiddle NTP4VCSplitRight
  NTP4VCOptionSeq NTP4VCRebuild
  NTP4VCSeq NTP4VCHgt NTP4VCNodeModel
  NTP4VCEq NTP4VCLt NTP4VCSelectionPossible
  NTP4VCSelected NTP4VCDomain
$.

ntp4vc-tree-empty-syntax $a class NTP4VCTreeEmpty $.
ntp4vc-tree-node-syntax
  $a class ( NTP4VCTreeNode A B C D ) $.

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

ntp4vc-seq-syntax $a class ( NTP4VCSeq A ) $.
ntp4vc-hgt-syntax $a class ( NTP4VCHgt A ) $.
ntp4vc-node-model-syntax $a class ( NTP4VCNodeModel A B C ) $.

ntp4vc-eq-syntax $a wff ( NTP4VCEq A B C ) $.
ntp4vc-lt-syntax $a wff ( NTP4VCLt A B C ) $.
ntp4vc-selection-possible-syntax
  $a wff ( NTP4VCSelectionPossible A B C D ) $.
ntp4vc-selected-syntax
  $a wff ( NTP4VCSelected A B C D E ) $.
ntp4vc-domain-syntax
  $a wff ( NTP4VCDomain A B C D ) $.

ntp4vc-tree-empty-def $a |- NTP4VCTreeEmpty = <. 2 , (/) >. $.

ntp4vc-tree-node-def $a |- ( NTP4VCTreeNode A B C D ) =
  <. 3 , <. A , <. B , <. C , D >. >. >. >. $.

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
  $d d i A B C D E $.

  ntp4vc-selected-def $a |- (
    ( NTP4VCSelected A B C D E )
    <->
    (
      A. i e. ZZ
        (
          ( 0 <_ i /\ i < ( # ` ( NTP4VCSplitLeft B ) ) )
          ->
          (
            NTP4VCLt
              ( C ` ( ( NTP4VCSplitLeft B ) ` i ) )
              A D
          )
        )
      /\
      (
        A. i e. ZZ
          (
            ( 0 <_ i /\ i < ( # ` ( NTP4VCSplitRight B ) ) )
            ->
            (
              NTP4VCLt
                A
                ( C ` ( ( NTP4VCSplitRight B ) ` i ) )
                D
            )
          )
        /\
        (
          ( NTP4VCSplitMiddle B ) = NTP4VCNone
          \/
          E. d e. E
            (
              ( NTP4VCSplitMiddle B ) = ( NTP4VCSome d )
              /\
              ( NTP4VCEq A ( C ` d ) D )
            )
        )
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
        (/) ( NTP4VCSeq ( J ` ( O ` x ) ) ) H I
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

  $( Source theorem parameters A=t5 and B=k. $)
  ntp4vc-t5-type $e |- A e. F $.
  ntp4vc-k-type $e |- B e. C $.

  ntp4vc-pearl-avl-tables-mapbase-get-vc $a |- (
    (
      NTP4VCSelectionPossible
        B ( NTP4VCSeq ( J ` ( O ` A ) ) ) H I
    )
    /\
    A. o e. ( NTP4VCSplit D )
      A. r e. ( NTP4VCOption D )
        (
          (
            (
              ( NTP4VCSelected B o H I D )
              /\
              (
                ( NTP4VCRebuild o )
                =
                ( NTP4VCSeq ( J ` ( O ` A ) ) )
              )
            )
            /\
            (
              (
                r = NTP4VCNone
                /\
                ( NTP4VCSplitMiddle o ) = NTP4VCNone
              )
              \/
              E. d e. D
                (
                  r = ( NTP4VCSome d )
                  /\
                  ( NTP4VCSplitMiddle o ) = ( NTP4VCSome d )
                )
            )
          )
          ->
          (
            (
              r = NTP4VCNone
              /\
              -.
              (
                NTP4VCDomain
                  ( NTP4VCSeq ( J ` ( O ` A ) ) )
                  B H I
              )
            )
            \/
            E. d e. D
              (
                r = ( NTP4VCSome d )
                /\
                (
                  0 < ( # ` ( NTP4VCSeq ( J ` ( O ` A ) ) ) )
                  /\
                  (
                    ( NTP4VCEq ( H ` d ) B I )
                    /\
                    (
                      (
                        NTP4VCDomain
                          ( NTP4VCSeq ( J ` ( O ` A ) ) )
                          B H I
                      )
                      /\
                      (
                        P
                        `
                        <.
                          ( NTP4VCSeq ( J ` ( O ` A ) ) ) ,
                          B
                        >.
                      )
                      =
                      d
                    )
                  )
                )
              )
          )
        )
  ) $.
$}
