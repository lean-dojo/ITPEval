$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/dijkstra_DijkstraShortestPath_shortest_path_codeqtvc: the Dijkstra
  shortest-path verification condition initializes the visited and frontier
  invariants, preserves them through minimum extraction and edge relaxation,
  proves the termination measures decrease, and specifies the final reachable
  and unreachable vertices. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V, S, and D are arbitrary nonempty carriers for vertices, source set
  wrappers, and integer distance maps. T maps every set wrapper to an actual
  finite subset of V, and H is the source choice operation with its nonempty
  choice specification. G is the finite graph-vertex set, J maps each vertex
  to its finite successor set inside G, and W is the everywhere-nonnegative
  integer weight function.

  C, Q, R, and U are respectively contents, create, lookup, and update for
  integer distance maps. Their pointwise source specifications are retained
  exactly, including update at one vertex and preservation everywhere else.

  NTP4VCPath is bidirectionally equivalent to the source inductive weighted
  path relation: an empty word is the zero path at one vertex, while a
  nonempty finite word records all vertices before the endpoint, every
  successor edge, and the sum of all edge weights. The remaining named
  predicates directly expand min, shortest_path, inv_src, inv, inv_succ, and
  inv_succ2. Source let-bindings are substituted definitionally.

  Proposition-valued conditionals are represented by the conjunction of
  their true-guard and false-guard implications. This is a bidirectional
  classical equivalence and preserves every internal quantifier, including
  the chosen successor, updated frontier and map values, and all loop-state
  objects. Splitting the theorem's outer implication into scoped essential
  hypotheses is likewise equivalent to the source statement. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p declaration.
$)

$c
  NTP4VCPath NTP4VCMin NTP4VCShortestPath NTP4VCInvSrc
  NTP4VCInv NTP4VCInvSucc NTP4VCInvSucc2 NTP4VCBelowMin
  NTP4VCRelaxCase NTP4VCInnerLoop NTP4VCSuccProcess
  NTP4VCVisitedStep NTP4VCExtractStep NTP4VCMainLoop
$.

ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D E F ) $.
ntp4vc-min-syntax
  $a wff ( NTP4VCMin A B C D E ) $.
ntp4vc-shortest-path-syntax
  $a wff ( NTP4VCShortestPath A B C D E F ) $.
ntp4vc-inv-src-syntax
  $a wff ( NTP4VCInvSrc A B C D ) $.
ntp4vc-inv-syntax
  $a wff ( NTP4VCInv A B C D E F G H I J ) $.
ntp4vc-inv-succ-syntax
  $a wff ( NTP4VCInvSucc A B C D E F G H I ) $.
ntp4vc-inv-succ2-syntax
  $a wff ( NTP4VCInvSucc2 A B C D E F G H I J K ) $.
ntp4vc-below-min-syntax
  $a wff ( NTP4VCBelowMin A B C D E F G H I ) $.
ntp4vc-relax-case-syntax
  $a wff ( NTP4VCRelaxCase A B C D E F G H I J K ) $.
ntp4vc-inner-loop-syntax
  $a wff (
    NTP4VCInnerLoop A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-succ-process-syntax
  $a wff (
    NTP4VCSuccProcess A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-visited-step-syntax
  $a wff (
    NTP4VCVisitedStep A B C D E F G H I J K L M N O P Q
  ) $.
ntp4vc-extract-step-syntax
  $a wff (
    NTP4VCExtractStep A B C D E F G H I J K L M N O P
  ) $.
ntp4vc-main-loop-syntax
  $a wff (
    NTP4VCMainLoop A B C D E F G H I J K L M N
  ) $.

${
  $d k l A B C D E F $.

  ntp4vc-path-def $a |- (
    NTP4VCPath A B C D E F
  ) <-> (
    E. l e. Word A
      (
        (
          ( # ` l ) = 0
          /\
          (
            D = E
            /\
            F = 0
          )
        )
        \/
        (
          0 < ( # ` l )
          /\
          (
            ( l ` 0 ) = D
            /\
            (
              A. k e. ( 0 ..^ ( ( # ` l ) - 1 ) )
                ( l ` ( k + 1 ) ) e. ( B ` ( l ` k ) )
              /\
              (
                E e. ( B ` ( l ` ( ( # ` l ) - 1 ) ) )
                /\
                F =
                  (
                    sum_ k e. ( 0 ..^ ( ( # ` l ) - 1 ) )
                      (
                        C
                        `
                        <. ( l ` k ) , ( l ` ( k + 1 ) ) >.
                      )
                    +
                    (
                      C
                      `
                      <. ( l ` ( ( # ` l ) - 1 ) ) , E >.
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
  $d x A B C D E $.

  ntp4vc-min-def $a |- (
    NTP4VCMin A B C D E
  ) <-> (
    C e. ( A ` D )
    /\
    A. x e. ( A ` D )
      (
        ( B ` <. E , C >. )
        <_
        ( B ` <. E , x >. )
      )
  ) $.
$}

${
  $d n A B C D E F $.

  ntp4vc-shortest-path-def $a |- (
    NTP4VCShortestPath A B C D E F
  ) <-> (
    ( NTP4VCPath A B C D E F )
    /\
    A. n e. ZZ
      (
        ( NTP4VCPath A B C D E n )
        ->
        F <_ n
      )
  ) $.
$}

ntp4vc-inv-src-def $a |- (
  NTP4VCInvSrc A B C D
) <-> (
  B e. ( A ` C )
  \/
  B e. ( A ` D )
) $.

${
  $d x A B C D E F G H I J $.

  ntp4vc-inv-def $a |- (
    NTP4VCInv A B C D E F G H I J
  ) <-> (
    ( NTP4VCInvSrc C G H I )
    /\
    (
      ( D ` <. J , G >. ) = 0
      /\
      (
        ( C ` H ) C_ B
        /\
        (
          ( C ` I ) C_ B
          /\
          (
            A. x e. A
              (
                x e. ( C ` I )
                ->
                -. x e. ( C ` H )
              )
            /\
            (
              A. x e. A
                (
                  x e. ( C ` H )
                  ->
                  (
                    NTP4VCShortestPath
                      A E F G x ( D ` <. J , x >. )
                  )
                )
              /\
              A. x e. A
                (
                  x e. ( C ` I )
                  ->
                  (
                    NTP4VCPath
                      A E F G x ( D ` <. J , x >. )
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
  $d x y A B C D E F G H I $.

  ntp4vc-inv-succ-def $a |- (
    NTP4VCInvSucc A B C D E F G H I
  ) <-> (
    A. x e. A
      (
        x e. ( B ` G )
        ->
        A. y e. A
          (
            y e. ( D ` x )
            ->
            (
              (
                y e. ( B ` G )
                \/
                y e. ( B ` H )
              )
              /\
              (
                ( C ` <. I , y >. )
                <_
                (
                  ( C ` <. I , x >. )
                  +
                  ( E ` <. x , y >. )
                )
              )
            )
          )
      )
  ) $.
$}

${
  $d x y A B C D E F G H I J K $.

  ntp4vc-inv-succ2-def $a |- (
    NTP4VCInvSucc2 A B C D E F G H I J K
  ) <-> (
    A. x e. A
      (
        x e. ( B ` G )
        ->
        A. y e. A
          (
            y e. ( D ` x )
            ->
            (
              (
                x =/= J
                \/
                (
                  x = J
                  /\
                  -. y e. ( B ` K )
                )
              )
              ->
              (
                (
                  y e. ( B ` G )
                  \/
                  y e. ( B ` H )
                )
                /\
                (
                  ( C ` <. I , y >. )
                  <_
                  (
                    ( C ` <. I , x >. )
                    +
                    ( E ` <. x , y >. )
                  )
                )
              )
            )
          )
      )
  ) $.
$}

${
  $d m n x A B C D E F G H I $.

  ntp4vc-below-min-def $a |- (
    NTP4VCBelowMin A B C D E F G H I
  ) <-> (
    A. m e. A
      (
        ( NTP4VCMin B C m H I )
        ->
        A. x e. A A. n e. ZZ
          (
            ( NTP4VCPath A D E F x n )
            ->
            (
              n < ( C ` <. I , m >. )
              ->
              x e. ( B ` G )
            )
          )
      )
  ) $.
$}

ntp4vc-relax-case-def $a |- (
  NTP4VCRelaxCase A B C D E F G H I J K
) <-> (
  (
    E e. ( A ` F )
    /\
    (
      I = G
      /\
      J = H
    )
  )
  \/
  (
    E e. ( A ` I )
    /\
    (
      ( B ` <. J , E >. )
      <_
      (
        ( B ` <. J , K >. )
        +
        ( D ` <. K , E >. )
      )
      /\
      (
        I = G
        /\
        J = H
      )
    )
  )
  \/
  (
    E e. ( A ` I )
    /\
    (
      (
        ( B ` <. H , K >. )
        +
        ( D ` <. K , E >. )
      )
      <
      ( B ` <. H , E >. )
      /\
      (
        I = G
        /\
        J =
          (
            C
            `
            <.
              H ,
              <.
                E ,
                (
                  ( B ` <. H , K >. )
                  +
                  ( D ` <. K , E >. )
                )
              >.
            >.
          )
      )
    )
  )
  \/
  (
    -. E e. ( A ` F )
    /\
    (
      -. E e. ( A ` G )
      /\
      (
        ( A ` I ) = ( { E } u. ( A ` G ) )
        /\
        J =
          (
            C
            `
            <.
              H ,
              <.
                E ,
                (
                  ( B ` <. H , K >. )
                  +
                  ( D ` <. K , E >. )
                )
              >.
            >.
          )
      )
    )
  )
) $.

${
  $d e m n q s x
     A B C D E F G H I J K L M N O P Q $.

  ntp4vc-inner-loop-def $a |- (
    NTP4VCInnerLoop A B C D E F G H I J K L M N O P Q
  ) <-> (
    (
      ( D ` Q ) =/= (/)
      ->
      (
        ( D ` Q ) =/= (/)
        /\
        A. s e. C
          (
            (
              ( E ` Q ) e. ( D ` Q )
              /\
              ( D ` s ) = ( ( D ` Q ) \ { ( E ` Q ) } )
            )
            ->
            A. q e. C A. m e. F
              (
                (
                  NTP4VCRelaxCase
                    D G H J ( E ` Q ) M N O q m P
                )
                ->
                (
                  (
                    0 <_ ( # ` ( D ` Q ) )
                    /\
                    ( # ` ( D ` s ) ) < ( # ` ( D ` Q ) )
                  )
                  /\
                  (
                    ( D ` s ) C_ ( I ` P )
                    /\
                    (
                      (
                        NTP4VCInv
                          A B D G I J K M q m
                      )
                      /\
                      (
                        NTP4VCInvSucc2
                          A D G I J K M q m P s
                      )
                    )
                  )
                )
              )
          )
      )
    )
    /\
    (
      ( D ` Q ) = (/)
      ->
      (
        (
          0 <_ ( ( # ` B ) - ( # ` ( D ` L ) ) )
          /\
          (
            ( ( # ` B ) - ( # ` ( D ` M ) ) )
            <
            ( ( # ` B ) - ( # ` ( D ` L ) ) )
          )
        )
        /\
        (
          ( NTP4VCInv A B D G I J K M N O )
          /\
          (
            ( NTP4VCInvSucc A D G I J K M N O )
            /\
            (
              NTP4VCBelowMin
                A D G I J K M N O
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d m q s
     A B C D E F G H I J K L M N O P Q $.

  ntp4vc-succ-process-def $a |- (
    NTP4VCSuccProcess A B C D E F G H I J K L M N O P Q
  ) <-> (
    ( D ` Q ) = ( I ` P )
    ->
    (
      (
        ( D ` Q ) C_ ( I ` P )
        /\
        (
          ( NTP4VCInv A B D G I J K M N O )
          /\
          (
            NTP4VCInvSucc2
              A D G I J K M N O P Q
          )
        )
      )
      /\
      A. s e. C A. q e. C A. m e. F
        (
          (
            ( D ` s ) C_ ( I ` P )
            /\
            (
              ( NTP4VCInv A B D G I J K M q m )
              /\
              (
                NTP4VCInvSucc2
                  A D G I J K M q m P s
              )
            )
          )
          ->
          (
            NTP4VCInnerLoop
              A B C D E F G H I J K L M q m P s
          )
        )
    )
  ) $.
$}

${
  $d s A B C D E F G H I J K L M N O P Q $.

  ntp4vc-visited-step-def $a |- (
    NTP4VCVisitedStep A B C D E F G H I J K L M N O P Q
  ) <-> (
    (
      ( D ` Q ) = ( { P } u. ( D ` L ) )
      /\
      (
        (
          P e. ( D ` L )
          ->
          ( # ` ( D ` Q ) ) = ( # ` ( D ` L ) )
        )
        /\
        (
          -. P e. ( D ` L )
          ->
          (
            ( # ` ( D ` Q ) )
            =
            ( ( # ` ( D ` L ) ) + 1 )
          )
        )
      )
    )
    ->
    A. s e. C
      (
        NTP4VCSuccProcess
          A B C D E F G H I J K L Q O N P s
      )
  ) $.
$}

${
  $d s A B C D E F G H I J K L M N O P $.

  ntp4vc-extract-step-def $a |- (
    NTP4VCExtractStep A B C D E F G H I J K L M N O P
  ) <-> (
    (
      ( NTP4VCMin D G P M N )
      /\
      ( D ` O ) = ( ( D ` M ) \ { P } )
    )
    ->
    A. s e. C
      (
        NTP4VCVisitedStep
          A B C D E F G H I J K L M N O P s
      )
  ) $.
$}

${
  $d m q s x
     A B C D E F G H I J K L M N $.

  ntp4vc-main-loop-def $a |- (
    NTP4VCMainLoop A B C D E F G H I J K L M N
  ) <-> (
    (
      (
        ( NTP4VCInv A B D G I J K N L M )
        /\
        (
          ( NTP4VCInvSucc A D G I J K N L M )
          /\
          (
            NTP4VCBelowMin
              A D G I J K N L M
          )
        )
      )
      ->
      (
        (
          ( D ` L ) =/= (/)
          ->
          (
            ( D ` L ) =/= (/)
            /\
            A. q e. C A. x e. A
              (
                NTP4VCExtractStep
                  A B C D E F G H I J K N L M q x
              )
          )
        )
        /\
        (
          ( D ` L ) = (/)
          ->
          (
            A. x e. A
              (
                x e. ( D ` N )
                ->
                (
                  NTP4VCShortestPath
                    A I J K x ( G ` <. M , x >. )
                )
              )
            /\
            A. x e. A
              (
                -. x e. ( D ` N )
                ->
                A. m e. ZZ
                  -.
                  ( NTP4VCPath A I J K x m )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d k m q s x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary inhabited source carriers. $)
  ntp4vc-vertex-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-set-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-map-carrier-nonempty $e |- D =/= (/) $.

  $( Finite graph vertices, finite successors, and nonnegative weights. $)
  ntp4vc-vertices-subset $e |- G C_ V $.
  ntp4vc-vertices-finite $e |- G e. Fin $.
  ntp4vc-successor-function
    $e |- J e. ( ( ~P V ) ^m V ) $.
  ntp4vc-successors-finite $e |- A. x e. V ( J ` x ) e. Fin $.
  ntp4vc-successors-in-vertices $e |- A. x e. V ( J ` x ) C_ G $.
  ntp4vc-weight-function $e |- W e. ( ZZ ^m ( V X. V ) ) $.
  ntp4vc-weight-nonnegative $e |- A. x e. V A. y e. V
    0 <_ ( W ` <. x , y >. ) $.

  $( Source finite-set wrapper and choice operation. $)
  ntp4vc-to-fset-function
    $e |- T e. ( ( ~P V ) ^m S ) $.
  ntp4vc-to-fset-finite $e |- A. x e. S ( T ` x ) e. Fin $.
  ntp4vc-choose-function $e |- H e. ( V ^m S ) $.
  ntp4vc-choose-spec $e |- A. x e. S
    (
      ( T ` x ) =/= (/)
      ->
      ( H ` x ) e. ( T ` x )
    ) $.

  $( Source integer-map operations and their exact specifications. $)
  ntp4vc-contents-function
    $e |- C e. ( ZZ ^m ( D X. V ) ) $.
  ntp4vc-create-function $e |- Q e. ( D ^m ZZ ) $.
  ntp4vc-lookup-function
    $e |- R e. ( ZZ ^m ( D X. V ) ) $.
  ntp4vc-update-function
    $e |- U e. ( D ^m ( D X. ( V X. ZZ ) ) ) $.

  ntp4vc-create-spec $e |- A. m e. ZZ A. x e. V
    (
      C ` <. ( Q ` m ) , x >.
    ) = m $.

  ntp4vc-lookup-spec $e |- A. m e. D A. x e. V
    (
      R ` <. m , x >.
    ) = (
      C ` <. m , x >.
    ) $.

  ntp4vc-update-spec $e |- A. m e. D A. x e. V
    A. n e. ZZ A. y e. V
      (
        C ` <.
          ( U ` <. m , <. x , n >. >. ) ,
          y
        >.
      )
      =
      if (
        y = x ,
        n ,
        ( C ` <. m , y >. )
      ) $.

  $( Source theorem parameters and fact0--fact3. $)
  ntp4vc-src-vertex $e |- A e. V $.
  ntp4vc-dst-vertex $e |- B e. V $.
  ntp4vc-visited-set $e |- E e. S $.
  ntp4vc-frontier-set $e |- F e. S $.
  ntp4vc-distance-map $e |- I e. D $.

  ntp4vc-fact0 $e |- A e. G $.
  ntp4vc-fact1 $e |- B e. G $.
  ntp4vc-fact2 $e |- ( T ` E ) = (/) $.
  ntp4vc-fact3 $e |- ( T ` F ) = { A } $.

  ntp4vc-pearl-dijkstra-shortest-path-code-vc $a |- (
    (
      NTP4VCInv
        V G T R J W A E F
        ( U ` <. I , <. A , 0 >. >. )
    )
    /\
    (
      (
        NTP4VCInvSucc
          V T R J W A E F
          ( U ` <. I , <. A , 0 >. >. )
      )
      /\
      (
        (
          NTP4VCBelowMin
            V T R J W A E F
            ( U ` <. I , <. A , 0 >. >. )
        )
        /\
        A. q e. S A. m e. D A. s e. S
          (
            NTP4VCMainLoop
              V G S T H D R U J W A q m s
          )
      )
    )
  ) $.
$}
