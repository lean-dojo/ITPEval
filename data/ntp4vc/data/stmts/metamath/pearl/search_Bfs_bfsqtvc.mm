$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/search_Bfs_bfsqtvc: the breadth-first-search verification condition
  establishes and preserves frontier path-length, coverage, minimality, and
  successor-collection invariants, with successful return or exhaustion of
  all reachable successful states. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V is the arbitrary nonempty source state carrier. M is the total function
  sending every state to its finite word of successor states, A is the
  distinguished start state, and S is the arbitrary success predicate,
  represented extensionally as a subset of V. SetMM words over V are exactly
  arbitrary finite zero-based source sequences.

  NTP4VCToNat and NTP4VCAt reproduce the exports' integer-to-natural
  conversion and inhabited totalized sequence lookup. NTP4VCMove directly
  expands the source existential successor-index predicate.

  NTP4VCPath is bidirectionally equivalent to the source inductive path
  relation: a finite word of n+1 states starts at the source, ends at the
  target, and has a source move between each consecutive pair. For n=0 this
  is Path0; each edge is Path1; concatenation is Patht. Conversely induction
  over those constructors produces exactly such a finite word.

  The remaining named predicates are definitional groupings of the outer BFS
  invariant, inner successor-collection invariant, append contract, one
  for-loop step, complete for-loop obligation, nonempty-layer obligation, and
  no-solution branch. Source let-bindings are substituted definitionally.
  Proposition-valued conditionals are represented by their equivalent guarded
  true and false implications. Every state, integer, and finite-word
  quantifier retains its full source domain. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCMove NTP4VCPath
  NTP4VCLevelInvariant NTP4VCInnerInvariant NTP4VCAppendSpec
  NTP4VCProcessStep NTP4VCForObligation NTP4VCNonemptyObligation
  NTP4VCNoReachableSuccess NTP4VCOuterStep
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-move-syntax
  $a wff ( NTP4VCMove A B C D ) $.
ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D E ) $.
ntp4vc-level-invariant-syntax
  $a wff ( NTP4VCLevelInvariant A B C D E F ) $.
ntp4vc-inner-invariant-syntax
  $a wff ( NTP4VCInnerInvariant A B C D E F ) $.
ntp4vc-append-spec-syntax
  $a wff ( NTP4VCAppendSpec A B C D ) $.
ntp4vc-process-step-syntax
  $a wff ( NTP4VCProcessStep A B C D E F G H ) $.
ntp4vc-for-obligation-syntax
  $a wff ( NTP4VCForObligation A B C D E F G H ) $.
ntp4vc-nonempty-obligation-syntax
  $a wff ( NTP4VCNonemptyObligation A B C D E F ) $.
ntp4vc-no-reachable-success-syntax
  $a wff ( NTP4VCNoReachableSuccess A B C D ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C D E F ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat C ) < ( # ` B ) ,
  ( B ` ( NTP4VCToNat C ) ) ,
  A
) $.

${
  $d i A B C D $.

  ntp4vc-move-definition $a |- (
    NTP4VCMove A B C D
  ) <-> (
    E. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` ( A ` C ) )
        )
        /\
        D = ( NTP4VCAt B ( A ` C ) i )
      )
  ) $.
$}

${
  $d k l A B C D E $.

  ntp4vc-path-definition $a |- (
    NTP4VCPath A B C D E
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
              (
                NTP4VCMove
                  B C ( l ` k ) ( l ` ( k + 1 ) )
              )
          )
        )
      )
  ) $.
$}

${
  $d i n t A B C D E F $.

  ntp4vc-level-invariant-definition $a |- (
    NTP4VCLevelInvariant A B C D E F
  ) <-> (
    0 <_ E
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` F )
          )
          ->
          (
            NTP4VCPath
              A B C ( NTP4VCAt C F i ) E
          )
        )
      /\
      (
        A. t e. A
          (
            ( NTP4VCPath A B C t E )
            ->
            t e. ran F
          )
        /\
        A. t e. A A. n e. ZZ
          (
            ( NTP4VCPath A B C t n )
            ->
            (
              t e. D
              ->
              E <_ n
            )
          )
      )
    )
  ) $.
$}

${
  $d j k l A B C D E F $.

  ntp4vc-inner-invariant-definition $a |- (
    NTP4VCInnerInvariant A B C D E F
  ) <-> (
    A. l e. ZZ
      (
        (
          0 <_ l
          /\
          l < ( # ` E )
        )
        ->
        E. j e. ZZ
          (
            (
              0 <_ j
              /\
              j < F
            )
            /\
            (
              NTP4VCMove
                B C
                ( NTP4VCAt C D j )
                ( NTP4VCAt C E l )
            )
          )
      )
    /\
    (
      A. j e. ZZ A. k e. ZZ
        (
          (
            0 <_ j
            /\
            j < F
          )
          ->
          (
            (
              0 <_ k
              /\
              k <
                (
                  # `
                  ( B ` ( NTP4VCAt C D j ) )
                )
            )
            ->
            (
              NTP4VCAt
                C
                ( B ` ( NTP4VCAt C D j ) )
                k
            ) e. ran E
          )
        )
      /\
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < F
          )
          ->
          -. ( NTP4VCAt C D j ) e. A
        )
    )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-append-spec-definition $a |- (
    NTP4VCAppendSpec A B C D
  ) <-> (
    ( # ` D ) = ( ( # ` B ) + ( # ` C ) )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` B )
          )
          ->
          ( NTP4VCAt A D i ) = ( NTP4VCAt A B i )
        )
      /\
      A. i e. ZZ
        (
          (
            ( # ` B ) <_ i
            /\
            i < ( # ` D )
          )
          ->
          (
            NTP4VCAt A D i
          )
          =
          (
            NTP4VCAt A C ( i - ( # ` B ) )
          )
        )
    )
  ) $.
$}

ntp4vc-process-step-definition $a |- (
  NTP4VCProcessStep A B C D E F G H
) <-> (
  (
    ( NTP4VCAt C G H ) e. D
    ->
    (
      NTP4VCPath
        A B C ( NTP4VCAt C G H ) E
    )
  )
  /\
  (
    -. ( NTP4VCAt C G H ) e. D
    ->
    (
      (
        NTP4VCAppendSpec
          C
          ( B ` ( NTP4VCAt C G H ) )
          F
          (
            ( B ` ( NTP4VCAt C G H ) )
            ++
            F
          )
      )
      ->
      (
        NTP4VCInnerInvariant
          D B C G
          (
            ( B ` ( NTP4VCAt C G H ) )
            ++
            F
          )
          ( H + 1 )
      )
    )
  )
) $.

${
  $d i A B C D E F G H $.

  ntp4vc-for-obligation-definition $a |- (
    NTP4VCForObligation A B C D E F G H
  ) <-> (
    A. i e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i <_ G
          )
          /\
          ( NTP4VCInnerInvariant D B C F H i )
        )
        ->
        (
          NTP4VCProcessStep
            A B C D E H F i
        )
      )
    /\
    (
      ( NTP4VCInnerInvariant D B C F H ( G + 1 ) )
      ->
      (
        NTP4VCLevelInvariant
          A B C D ( E + 1 ) H
      )
    )
  ) $.
$}

${
  $d H A B C D E F $.

  ntp4vc-nonempty-obligation-definition $a |- (
    NTP4VCNonemptyObligation A B C D E F
  ) <-> (
    (
      0 <_ ( ( ( # ` F ) - 1 ) + 1 )
      ->
      (
        ( NTP4VCInnerInvariant D B C F (/) 0 )
        /\
        A. H e. Word A
          (
            NTP4VCForObligation
              A B C D E F ( ( # ` F ) - 1 ) H
          )
      )
    )
    /\
    (
      ( ( ( # ` F ) - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCLevelInvariant
          A B C D ( E + 1 ) (/)
      )
    )
  ) $.
$}

${
  $d n t A B C D $.

  ntp4vc-no-reachable-success-definition $a |- (
    NTP4VCNoReachableSuccess A B C D
  ) <-> (
    A. t e. A A. n e. ZZ
      (
        t e. D
        ->
        -. ( NTP4VCPath A B C t n )
      )
  ) $.
$}

ntp4vc-outer-step-definition $a |- (
  NTP4VCOuterStep A B C D E F
) <-> (
  (
    0 < ( # ` F )
    ->
    ( NTP4VCNonemptyObligation A B C D E F )
  )
  /\
  (
    -. 0 < ( # ` F )
    ->
    ( NTP4VCNoReachableSuccess A B C D )
  )
) $.

${
  $d i p q
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source state carrier, moves, start state, and success predicate. $)
  ntp4vc-state-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-moves-function $e |- M e. ( ( Word V ) ^m V ) $.
  ntp4vc-start-state $e |- A e. V $.
  ntp4vc-success-predicate $e |- S C_ V $.

  $(
    The source let-bound old list, head, and new list are respectively
    empty, A, and the singleton word <" A ">. This is its explicit cons
    contract antecedent.
  $)
  ntp4vc-initial-cons-contract $e |- (
    ( # ` <" A "> ) = ( 1 + ( # ` (/) ) )
    /\
    (
      ( NTP4VCAt A <" A "> 0 ) = A
      /\
      A. i e. ZZ
        (
          (
            0 < i
            /\
            i <_ ( # ` (/) )
          )
          ->
          (
            NTP4VCAt A <" A "> i
          )
          =
          (
            NTP4VCAt A (/) ( i - 1 )
          )
        )
    )
  ) $.

  ntp4vc-pearl-search-bfs-vc $a |- (
    ( NTP4VCLevelInvariant V M A S 0 <" A "> )
    /\
    A. p e. ZZ A. q e. Word V
      (
        ( NTP4VCLevelInvariant V M A S p q )
        ->
        ( NTP4VCOuterStep V M A S p q )
      )
  ) $.
$}
