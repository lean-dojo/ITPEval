$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/vstte12_bfs_BFS_bfsqtvc: the breadth-first-search verification
  condition initializes and preserves shortest-path frontier, visited-node,
  successor-closure, target-discovery, and frontier-rotation invariants, or
  concludes that the target is unreachable. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V and S are the arbitrary nonempty source vertex and mutable-set carriers.
  M maps each vertex to its finite successor set, T maps each mutable-set
  value to its finite extensional vertex set, H is source choice, and R is
  the source equality predicate. Their exact source laws are explicit
  hypotheses of the final assertion.

  NTP4VCBFSPath is bidirectionally equivalent to the source inductive path
  relation: a word of n+1 vertices starts at the source, ends at the target,
  and follows M between every consecutive pair. The singleton word is
  path_empty, appending one successor is path_succ, and induction on either
  representation gives the converse. Thus the integer path-length domain,
  including the impossibility of negative path lengths, is preserved.

  The remaining named predicates directly group shortest_path, inv, closure,
  the complete loop invariant, the empty-frontier rotation, the fill_next
  postcondition, choose-and-remove processing, and the outer loop branch.
  Source let-bindings are substituted definitionally. Proposition-valued
  conditionals are represented by their equivalent guarded true and false
  implications. Cardinalities use SetMM's natural cardinal embedded in the
  integers, exactly matching the source casts. Every vertex, integer,
  mutable-set, finite-set, and finite-word quantifier retains its full source
  domain. All auxiliary assertions are syntax or faithful definitions; the
  final $a declaration is Metamath's native unproved statement encoding.
$)

$c
  NTP4VCBFSPath NTP4VCBFSShortestPath
  NTP4VCBFSInv NTP4VCBFSClosure NTP4VCBFSLayer
  NTP4VCBFSRotate NTP4VCBFSAfterFill
  NTP4VCBFSSelected NTP4VCBFSLoopCase
$.

ntp4vc-bfs-path-syntax
  $a wff ( NTP4VCBFSPath A B C D E ) $.
ntp4vc-bfs-shortest-path-syntax
  $a wff ( NTP4VCBFSShortestPath A B C D E ) $.
ntp4vc-bfs-inv-syntax
  $a wff ( NTP4VCBFSInv A B C D E F G H ) $.
ntp4vc-bfs-closure-syntax
  $a wff ( NTP4VCBFSClosure A B C D E F ) $.
ntp4vc-bfs-layer-syntax
  $a wff ( NTP4VCBFSLayer A B C D E F G H ) $.
ntp4vc-bfs-rotate-syntax
  $a wff ( NTP4VCBFSRotate A B C D E F G H I ) $.
ntp4vc-bfs-after-fill-syntax
  $a wff ( NTP4VCBFSAfterFill A B C D E F G H I ) $.
ntp4vc-bfs-selected-syntax
  $a wff ( NTP4VCBFSSelected A B C D E F G H I J K L M ) $.
ntp4vc-bfs-loop-case-syntax
  $a wff ( NTP4VCBFSLoopCase A B C D E F G H I J K L ) $.

${
  $d k l A B C D E $.

  ntp4vc-bfs-path-definition $a |- (
    NTP4VCBFSPath A B C D E
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

  ntp4vc-bfs-shortest-path-definition $a |- (
    NTP4VCBFSShortestPath A B C D E
  ) <-> (
    ( NTP4VCBFSPath A B C D E )
    /\
    A. m e. ZZ
      (
        m < E
        ->
        -. ( NTP4VCBFSPath A B C D m )
      )
  ) $.
$}

${
  $d m x A B C D E F G H $.

  ntp4vc-bfs-inv-definition $a |- (
    NTP4VCBFSInv A B C D E F G H
  ) <-> (
    F C_ E
    /\
    (
      A. x e. A
        (
          x e. F
          ->
          ( NTP4VCBFSShortestPath A B C x H )
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
              ( NTP4VCBFSShortestPath A B C x ( H + 1 ) )
            )
          /\
          (
            A. x e. A A. m e. ZZ
              (
                ( NTP4VCBFSPath A B C x m )
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
                      ( NTP4VCBFSPath A B C x m )
                      /\
                      m <_ ( H + 1 )
                    )
                )
              /\
              (
                A. x e. A
                  (
                    ( NTP4VCBFSShortestPath A B C x ( H + 1 ) )
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

  ntp4vc-bfs-closure-definition $a |- (
    NTP4VCBFSClosure A B C D E F
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
  $d x A B C D E F G H $.

  ntp4vc-bfs-layer-definition $a |- (
    NTP4VCBFSLayer A B C D E F G H
  ) <-> (
    ( NTP4VCBFSInv A B C D E F G H )
    /\
    (
      (
        F = (/)
        ->
        G = (/)
      )
      /\
      (
        A. x e. A
          ( NTP4VCBFSClosure A B E F G x )
        /\
        0 <_ H
      )
    )
  ) $.
$}

${
  $d q x A B C D E F G H I $.

  ntp4vc-bfs-rotate-definition $a |- (
    NTP4VCBFSRotate A B C D E F G H I
  ) <-> (
    A. q e. C
      (
        (
          ( D ` q ) = (/)
          /\
          ( # ` ( D ` q ) ) = 0
        )
        ->
        (
          ( NTP4VCBFSInv
              A B E F G H ( D ` q ) ( I + 1 ) )
          /\
          (
            (
              H = (/)
              ->
              ( D ` q ) = (/)
            )
            /\
            (
              A. x e. A
                ( NTP4VCBFSClosure A B G H ( D ` q ) x )
              /\
              0 <_ ( I + 1 )
            )
          )
        )
      )
  ) $.
$}

${
  $d q r x A B C D E F G H I $.

  ntp4vc-bfs-after-fill-definition $a |- (
    NTP4VCBFSAfterFill A B C D E F G H I
  ) <-> (
    A. q e. C A. r e. C
      (
        (
          (
            ( NTP4VCBFSInv
                A B E F ( D ` r ) ( D ` H ) ( D ` q ) G )
            /\
            ( B ` I ) C_ ( D ` r )
          )
          /\
          A. x e. A
            ( NTP4VCBFSClosure
                A B ( D ` r ) ( D ` H ) ( D ` q ) x )
        )
        ->
        (
          (
            ( D ` H ) = (/)
            ->
            ( NTP4VCBFSRotate
                A B C D E F ( D ` r ) ( D ` q ) G )
          )
          /\
          (
            ( D ` H ) =/= (/)
            ->
            ( NTP4VCBFSLayer
                A B E F ( D ` r ) ( D ` H ) ( D ` q ) G )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H I J K L M $.

  ntp4vc-bfs-selected-definition $a |- (
    NTP4VCBFSSelected A B C D E F G H I J K L M
  ) <-> (
    (
      M e. ( E ` J )
      /\
      ( E ` L ) = ( ( E ` J ) \ { M } )
    )
    ->
    (
      (
        <. M , G >. e. C
        <-> M = G
      )
      ->
      (
        (
          <. M , G >. e. C
          ->
          ( NTP4VCBFSShortestPath A B F G H )
        )
        /\
        (
          -. <. M , G >. e. C
          ->
          (
            (
              (
                ( NTP4VCBFSInv
                    A B F G ( E ` K ) ( E ` L ) ( E ` I ) H )
                /\
                ( NTP4VCBFSShortestPath A B F M H )
              )
              /\
              A. x e. A
                (
                  x =/= M
                  ->
                  ( NTP4VCBFSClosure
                      A B ( E ` K ) ( E ` L ) ( E ` I ) x )
                )
            )
            /\
            ( NTP4VCBFSAfterFill A B D E F G H L M )
          )
        )
      )
    )
  ) $.
$}

${
  $d n q A B C D E F G H I J K L $.

  ntp4vc-bfs-loop-case-definition $a |- (
    NTP4VCBFSLoopCase A B C D E F G H I J K L
  ) <-> (
    (
      ( E ` K ) =/= (/)
      ->
      (
        ( E ` K ) =/= (/)
        /\
        A. q e. D
          (
            NTP4VCBFSSelected
              A B C D E G H I J K L q ( F ` K )
          )
      )
    )
    /\
    (
      ( E ` K ) = (/)
      ->
      A. n e. ZZ
        -. ( NTP4VCBFSPath A B G H n )
    )
  ) $.
$}

${
  $d d q r u x y
     A B C D E F G H M R S T V $.

  $( Source carriers and Graph operations. $)
  ntp4vc-bfs-vertex-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-bfs-set-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-bfs-successor-function
    $e |- M e. ( ( ~P V ) ^m V ) $.
  ntp4vc-bfs-successor-finite $e |- A. x e. V
    ( M ` x ) e. Fin $.
  ntp4vc-bfs-to-fset-function
    $e |- T e. ( ( ~P V ) ^m S ) $.
  ntp4vc-bfs-to-fset-finite $e |- A. q e. S
    ( T ` q ) e. Fin $.
  ntp4vc-bfs-choose-function $e |- H e. ( V ^m S ) $.
  ntp4vc-bfs-choose-spec $e |- A. q e. S
    (
      ( T ` q ) =/= (/)
      ->
      ( H ` q ) e. ( T ` q )
    ) $.
  ntp4vc-bfs-equality-relation $e |- R C_ ( V X. V ) $.
  ntp4vc-bfs-equality-spec $e |- A. x e. V A. y e. V
    (
      <. x , y >. e. R
      <-> x = y
    ) $.

  $( Source bfs parameters. $)
  ntp4vc-bfs-source-vertex $e |- A e. V $.
  ntp4vc-bfs-target-vertex $e |- B e. V $.
  ntp4vc-bfs-visited-set $e |- C e. S $.
  ntp4vc-bfs-empty-current-set $e |- D e. S $.
  ntp4vc-bfs-empty-next-set $e |- E e. S $.
  ntp4vc-bfs-visited-after-insert $e |- F e. S $.
  ntp4vc-bfs-current-after-insert $e |- G e. S $.

  $( Exact generated postconditions fact0 through fact9. $)
  ntp4vc-bfs-fact0 $e |- ( T ` C ) = (/) $.
  ntp4vc-bfs-fact1 $e |- ( # ` ( T ` C ) ) = 0 $.
  ntp4vc-bfs-fact2 $e |- ( T ` D ) = (/) $.
  ntp4vc-bfs-fact3 $e |- ( # ` ( T ` D ) ) = 0 $.
  ntp4vc-bfs-fact4 $e |- ( T ` E ) = (/) $.
  ntp4vc-bfs-fact5 $e |- ( # ` ( T ` E ) ) = 0 $.
  ntp4vc-bfs-fact6 $e |- ( T ` F ) =
    ( ( T ` C ) u. { A } ) $.
  ntp4vc-bfs-fact7 $e |- (
    (
      A e. ( T ` C )
      ->
      ( # ` ( T ` F ) ) = ( # ` ( T ` C ) )
    )
    /\
    (
      -. A e. ( T ` C )
      ->
      ( # ` ( T ` F ) ) = ( ( # ` ( T ` C ) ) + 1 )
    )
  ) $.
  ntp4vc-bfs-fact8 $e |- ( T ` G ) =
    ( ( T ` D ) u. { A } ) $.
  ntp4vc-bfs-fact9 $e |- (
    (
      A e. ( T ` D )
      ->
      ( # ` ( T ` G ) ) = ( # ` ( T ` D ) )
    )
    /\
    (
      -. A e. ( T ` D )
      ->
      ( # ` ( T ` G ) ) = ( ( # ` ( T ` D ) ) + 1 )
    )
  ) $.

  ntp4vc-pearl-vstte12-bfs-bfs-vc $a |- (
    ( NTP4VCBFSLayer
        V M A B ( T ` F ) ( T ` G ) ( T ` E ) 0 )
    /\
    A. d e. ZZ A. q e. S A. r e. S A. u e. S
      (
        ( NTP4VCBFSLayer
            V M A B ( T ` u ) ( T ` r ) ( T ` q ) d )
        ->
        ( NTP4VCBFSLoopCase
            V M R S T H A B d q r u )
      )
  ) $.
$}
