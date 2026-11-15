$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_fill_nextqtvc: the breadth-first-search fill-next
  verification condition preserves shortest-path frontier and visited-set
  invariants while processing a finite successor accumulator, including
  closure, set-update, and cardinal-decrease obligations. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  V and S are the arbitrary nonempty source vertex and mutable-set carriers.
  M maps each vertex to its finite successor set, T maps each mutable-set
  value to its finite extensional vertex set, and H is the source choice
  function. Their exact source laws are explicit hypotheses of the final
  assertion.

  NTP4VCBFSFillPath is bidirectionally equivalent to the source inductive path
  relation: a word of n+1 vertices starts at the source, ends at the target,
  and follows M between every consecutive pair. The singleton word is
  path_empty, appending one successor is path_succ, and induction on either
  representation gives the converse. Thus the integer path-length domain,
  including the impossibility of negative path lengths, is preserved.

  The remaining named predicates directly group shortest_path, inv, closure,
  the fill_next loop invariant, and its complete conditional loop body.
  Source let-bindings are substituted definitionally. Proposition-valued
  conditionals are represented by their equivalent guarded true and false
  implications. Cardinalities use SetMM's natural cardinal, with its standard
  embedding in the integers where the source casts cardinalities. Every
  vertex, integer, mutable-set, finite-set, and finite-word quantifier retains
  its full source domain. All auxiliary assertions are syntax or faithful
  definitions; the final $a declaration is Metamath's native unproved
  statement encoding.
$)

$c
  NTP4VCBFSFillPath NTP4VCBFSFillShortestPath
  NTP4VCBFSFillInv NTP4VCBFSFillClosure
  NTP4VCBFSFillState NTP4VCBFSFillStep
$.

ntp4vc-bfs-fill-path-syntax
  $a wff ( NTP4VCBFSFillPath A B C D E ) $.
ntp4vc-bfs-fill-shortest-path-syntax
  $a wff ( NTP4VCBFSFillShortestPath A B C D E ) $.
ntp4vc-bfs-fill-inv-syntax
  $a wff ( NTP4VCBFSFillInv A B C D E F G H ) $.
ntp4vc-bfs-fill-closure-syntax
  $a wff ( NTP4VCBFSFillClosure A B C D E F ) $.
ntp4vc-bfs-fill-state-syntax
  $a wff ( NTP4VCBFSFillState A B C D E F G H I J ) $.
ntp4vc-bfs-fill-step-syntax
  $a wff ( NTP4VCBFSFillStep A B C D E F G H I J K L M ) $.

${
  $d k l A B C D E $.

  ntp4vc-bfs-fill-path-definition $a |- (
    NTP4VCBFSFillPath A B C D E
  ) <-> (
    0 <_ E
    /\
    E. l e. Word A
      (
        ( # ` l ) = ( E + 1 )
        /\
        (
          ( l ` 0 ) = C
          /\
          (
            ( l ` E ) = D
            /\
            A. k e. ( 0 ..^ E )
              ( l ` ( k + 1 ) ) e. ( B ` ( l ` k ) )
          )
        )
      )
  ) $.
$}

${
  $d m A B C D E $.

  ntp4vc-bfs-fill-shortest-path-definition $a |- (
    NTP4VCBFSFillShortestPath A B C D E
  ) <-> (
    ( NTP4VCBFSFillPath A B C D E )
    /\
    A. m e. ZZ
      (
        m < E
        ->
        -. ( NTP4VCBFSFillPath A B C D m )
      )
  ) $.
$}

${
  $d m x A B C D E F G H $.

  ntp4vc-bfs-fill-inv-definition $a |- (
    NTP4VCBFSFillInv A B C D E F G H
  ) <-> (
    F C_ E
    /\
    (
      A. x e. A
        (
          x e. F
          ->
          ( NTP4VCBFSFillShortestPath A B C x H )
        )
      /\
      (
        G C_ E
        /\
        (
          A. x e. A
            (
              x e. G
              ->
              ( NTP4VCBFSFillShortestPath A B C x ( H + 1 ) )
            )
          /\
          (
            A. x e. A A. m e. ZZ
              (
                ( NTP4VCBFSFillPath A B C x m )
                ->
                (
                  m <_ H
                  ->
                  x e. E
                )
              )
            /\
            (
              A. x e. A
                (
                  x e. E
                  ->
                  E. m e. ZZ
                    (
                      ( NTP4VCBFSFillPath A B C x m )
                      /\
                      m <_ ( H + 1 )
                    )
                )
              /\
              (
                A. x e. A
                  (
                    ( NTP4VCBFSFillShortestPath A B C x ( H + 1 ) )
                    ->
                    (
                      x e. G
                      \/
                      -. x e. E
                    )
                  )
                /\
                (
                  D e. E
                  ->
                  (
                    D e. F
                    \/
                    D e. G
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
  $d y A B C D E F $.

  ntp4vc-bfs-fill-closure-definition $a |- (
    NTP4VCBFSFillClosure A B C D E F
  ) <-> (
    F e. C
    ->
    (
      -. F e. D
      ->
      (
        -. F e. E
        ->
        A. y e. A
          (
            y e. ( B ` F )
            ->
            y e. C
          )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G H I J $.

  ntp4vc-bfs-fill-state-definition $a |- (
    NTP4VCBFSFillState A B C D E F G H I J
  ) <-> (
    ( NTP4VCBFSFillInv A B C D E F G H )
    /\
    (
      J C_ ( B ` I )
      /\
      (
        ( ( B ` I ) \ J ) C_ E
        /\
        A. x e. A
          (
            x =/= I
            ->
            ( NTP4VCBFSFillClosure A B E F G x )
          )
      )
    )
  ) $.
$}

${
  $d q r u x A B C D E F G H I J K L M $.

  ntp4vc-bfs-fill-step-definition $a |- (
    NTP4VCBFSFillStep A B C D E F G H I J K L M
  ) <-> (
    (
      ( D ` K ) =/= (/)
      ->
      (
        ( D ` K ) =/= (/)
        /\
        A. q e. C
          (
            (
              ( E ` K ) e. ( D ` K )
              /\
              ( D ` q ) = ( ( D ` K ) \ { E ` K } )
            )
            ->
            (
              (
                -. ( E ` K ) e. ( D ` M )
                ->
                A. r e. C
                  (
                    (
                      ( D ` r ) =
                        ( ( D ` M ) u. { E ` K } )
                      /\
                      (
                        (
                          ( E ` K ) e. ( D ` M )
                          ->
                          ( # ` ( D ` r ) ) =
                            ( # ` ( D ` M ) )
                        )
                        /\
                        (
                          -. ( E ` K ) e. ( D ` M )
                          ->
                          ( # ` ( D ` r ) ) =
                            ( ( # ` ( D ` M ) ) + 1 )
                        )
                      )
                    )
                    ->
                    A. u e. C
                      (
                        (
                          ( D ` u ) =
                            ( ( D ` L ) u. { E ` K } )
                          /\
                          (
                            (
                              ( E ` K ) e. ( D ` L )
                              ->
                              ( # ` ( D ` u ) ) =
                                ( # ` ( D ` L ) )
                            )
                            /\
                            (
                              -. ( E ` K ) e. ( D ` L )
                              ->
                              ( # ` ( D ` u ) ) =
                                ( ( # ` ( D ` L ) ) + 1 )
                            )
                          )
                        )
                        ->
                        (
                          (
                            0 <_ ( # ` ( D ` K ) )
                            /\
                            ( # ` ( D ` q ) ) <
                              ( # ` ( D ` K ) )
                          )
                          /\
                          ( NTP4VCBFSFillState
                              A B F G
                              ( D ` r ) H ( D ` u ) I J ( D ` q ) )
                        )
                      )
                  )
              )
              /\
              (
                ( E ` K ) e. ( D ` M )
                ->
                (
                  (
                    0 <_ ( # ` ( D ` K ) )
                    /\
                    ( # ` ( D ` q ) ) <
                      ( # ` ( D ` K ) )
                  )
                  /\
                  ( NTP4VCBFSFillState
                      A B F G
                      ( D ` M ) H ( D ` L ) I J ( D ` q ) )
                )
              )
            )
          )
      )
    )
    /\
    (
      ( D ` K ) = (/)
      ->
      (
        ( NTP4VCBFSFillInv
            A B F G ( D ` M ) H ( D ` L ) I )
        /\
        (
          ( B ` J ) C_ ( D ` M )
          /\
          A. x e. A
            ( NTP4VCBFSFillClosure
                A B ( D ` M ) H ( D ` L ) x )
        )
      )
    )
  ) $.
$}

${
  $d q r u x
     A B C D E F G H I M S T V $.

  $( Source carriers and finite-set interfaces. $)
  ntp4vc-bfs-fill-vertex-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-bfs-fill-set-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-bfs-fill-successor-function
    $e |- M e. ( ( ~P V ) ^m V ) $.
  ntp4vc-bfs-fill-successor-finite $e |- A. x e. V
    ( M ` x ) e. Fin $.
  ntp4vc-bfs-fill-to-fset-function
    $e |- T e. ( ( ~P V ) ^m S ) $.
  ntp4vc-bfs-fill-to-fset-finite $e |- A. q e. S
    ( T ` q ) e. Fin $.
  ntp4vc-bfs-fill-choose-function $e |- H e. ( V ^m S ) $.
  ntp4vc-bfs-fill-choose-spec $e |- A. q e. S
    (
      ( T ` q ) =/= (/)
      ->
      ( H ` q ) e. ( T ` q )
    ) $.

  $( Source fill_next parameters. $)
  ntp4vc-bfs-fill-source-vertex $e |- A e. V $.
  ntp4vc-bfs-fill-target-vertex $e |- B e. V $.
  ntp4vc-bfs-fill-visited-set $e |- C e. S $.
  ntp4vc-bfs-fill-current-set $e |- D e. S $.
  ntp4vc-bfs-fill-next-set $e |- E e. S $.
  ntp4vc-bfs-fill-depth $e |- F e. ZZ $.
  ntp4vc-bfs-fill-selected-vertex $e |- G e. V $.
  ntp4vc-bfs-fill-accumulator-set $e |- I e. S $.

  $( Exact generated hypotheses fact0 through fact3. $)
  ntp4vc-bfs-fill-fact0 $e |- (
    NTP4VCBFSFillInv
      V M A B ( T ` C ) ( T ` D ) ( T ` E ) F
  ) $.
  ntp4vc-bfs-fill-fact1 $e |- (
    NTP4VCBFSFillShortestPath V M A G F
  ) $.
  ntp4vc-bfs-fill-fact2 $e |- A. x e. V
    (
      x =/= G
      ->
      ( NTP4VCBFSFillClosure
          V M ( T ` C ) ( T ` D ) ( T ` E ) x )
    ) $.
  ntp4vc-bfs-fill-fact3 $e |- ( T ` I ) = ( M ` G ) $.

  ntp4vc-pearl-vstte12-bfs-fill-next-vc $a |- (
    ( NTP4VCBFSFillState
        V M A B ( T ` C ) ( T ` D ) ( T ` E ) F G ( T ` I ) )
    /\
    A. q e. S A. r e. S A. u e. S
      (
        ( NTP4VCBFSFillState
            V M A B ( T ` u ) ( T ` D ) ( T ` r ) F G ( T ` q ) )
        ->
        ( NTP4VCBFSFillStep
            V M S T H A B ( T ` D ) F G q r u )
      )
  ) $.
$}
