$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/search_Dfs_dfsqtvc: the depth-first-search verification condition
  covers depth exhaustion, immediate success, and preservation of the
  bounded no-solution invariant across recursive successor searches. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  V is the arbitrary nonempty source state carrier. M is the total function
  sending every state to its finite word of successor states, and S is the
  arbitrary success predicate, represented extensionally as a subset of V.
  SetMM words over V are exactly arbitrary finite zero-based source
  sequences.

  NTP4VCToNat and NTP4VCAt reproduce the exports' integer-to-natural
  conversion and inhabited totalized sequence lookup. NTP4VCMove directly
  expands the source existential successor-index predicate.

  NTP4VCPath is bidirectionally equivalent to the source inductive path
  relation: a finite word of n+1 states starts at the source, ends at the
  target, and has a source move between each consecutive pair. For n=0 this
  is Path0; each edge is Path1; concatenation is Patht. Conversely induction
  over those constructors produces exactly such a finite word.

  NTP4VCDfsNoSolution is the source NoSolution postcondition.
  NTP4VCDfsInvariant is the for-loop invariant, NTP4VCDfsStep is one
  recursive successor-search obligation, and NTP4VCDfsLoop is the complete
  for-loop verification condition. The universal source outcome match is
  expanded definitionally into its exhaustive NoSolution case and all
  Solution t n cases. Source let-bindings are substituted definitionally,
  and proposition-valued conditionals are represented by their equivalent
  guarded true and false implications. Every state, integer, and finite-word
  quantifier retains its full source domain. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCMove NTP4VCPath
  NTP4VCDfsNoSolution NTP4VCDfsInvariant
  NTP4VCDfsStep NTP4VCDfsLoop NTP4VCDfsCase
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-move-syntax
  $a wff ( NTP4VCMove A B C D ) $.
ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D E ) $.
ntp4vc-dfs-no-solution-syntax
  $a wff ( NTP4VCDfsNoSolution A B C D E ) $.
ntp4vc-dfs-invariant-syntax
  $a wff ( NTP4VCDfsInvariant A B C D E F G ) $.
ntp4vc-dfs-step-syntax
  $a wff ( NTP4VCDfsStep A B C D E F G ) $.
ntp4vc-dfs-loop-syntax
  $a wff ( NTP4VCDfsLoop A B C D E F ) $.
ntp4vc-dfs-case-syntax
  $a wff ( NTP4VCDfsCase A B C D E F ) $.

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
  $d n t A B C D E $.

  ntp4vc-dfs-no-solution-definition $a |- (
    NTP4VCDfsNoSolution A B C D E
  ) <-> (
    A. t e. A A. n e. ZZ
      (
        (
          0 <_ n
          /\
          n <_ E
        )
        ->
        (
          t e. C
          ->
          -. ( NTP4VCPath A B D t n )
        )
      )
  ) $.
$}

${
  $d j n t A B C D E F G $.

  ntp4vc-dfs-invariant-definition $a |- (
    NTP4VCDfsInvariant A B C D E F G
  ) <-> (
    A. j e. ZZ A. t e. A A. n e. ZZ
      (
        (
          0 <_ j
          /\
          j < F
        )
        ->
        (
          (
            NTP4VCPath
              A B ( NTP4VCAt D E j ) t n
          )
          ->
          (
            t e. C
            ->
            -.
              (
                0 <_ n
                /\
                n < G
              )
          )
        )
      )
  ) $.
$}

${
  $d n t A B C D E F G $.

  ntp4vc-dfs-step-definition $a |- (
    NTP4VCDfsStep A B C D E F G
  ) <-> (
    (
      (
        (
          0 <_ ( F - E )
          /\
          ( F - ( E + 1 ) ) < ( F - E )
        )
        /\
        0 <_ ( E + 1 )
      )
      /\
      ( E + 1 ) <_ ( F + 1 )
    )
    /\
    (
      (
        (
          NTP4VCDfsNoSolution
            A B C
            ( NTP4VCAt D ( B ` D ) G )
            ( F - ( E + 1 ) )
        )
        ->
        (
          NTP4VCDfsInvariant
            A B C D ( B ` D ) ( G + 1 ) ( F - E )
        )
      )
      /\
      A. t e. A A. n e. ZZ
        (
          (
            (
              NTP4VCPath
                A B
                ( NTP4VCAt D ( B ` D ) G )
                t n
            )
            /\
            (
              t e. C
              /\
              (
                0 <_ n
                /\
                n <_ ( F - ( E + 1 ) )
              )
            )
          )
          ->
          (
            ( NTP4VCPath A B D t ( n + 1 ) )
            /\
            (
              t e. C
              /\
              (
                0 <_ ( n + 1 )
                /\
                ( n + 1 ) <_ ( F - E )
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d i A B C D E F $.

  ntp4vc-dfs-loop-definition $a |- (
    NTP4VCDfsLoop A B C D E F
  ) <-> (
    (
      (
        0 <_
          (
            ( ( # ` ( B ` D ) ) - 1 )
            + 1
          )
        ->
        (
          (
            NTP4VCDfsInvariant
              A B C D ( B ` D ) 0 ( F - E )
          )
          /\
          A. i e. ZZ
            (
              (
                (
                  0 <_ i
                  /\
                  i <_ ( ( # ` ( B ` D ) ) - 1 )
                )
                /\
                (
                  NTP4VCDfsInvariant
                    A B C D ( B ` D ) i ( F - E )
                )
              )
              ->
              ( NTP4VCDfsStep A B C D E F i )
            )
        )
      )
      /\
      (
        (
          NTP4VCDfsInvariant
            A B C D ( B ` D )
            ( ( ( # ` ( B ` D ) ) - 1 ) + 1 )
            ( F - E )
        )
        ->
        ( NTP4VCDfsNoSolution A B C D ( F - E ) )
      )
    )
    /\
    (
      (
        (
          ( # ` ( B ` D ) ) - 1
        )
        + 1
      )
      < 0
      ->
      ( NTP4VCDfsNoSolution A B C D ( F - E ) )
    )
  ) $.
$}

ntp4vc-dfs-case-definition $a |- (
  NTP4VCDfsCase A B C D E F
) <-> (
  (
    F < E
    ->
    ( NTP4VCDfsNoSolution A B C D ( F - E ) )
  )
  /\
  (
    -. F < E
    ->
    (
      (
        D e. C
        ->
        (
          ( NTP4VCPath A B D D 0 )
          /\
          (
            D e. C
            /\
            (
              0 <_ 0
              /\
              0 <_ ( F - E )
            )
          )
        )
      )
      /\
      (
        -. D e. C
        ->
        ( NTP4VCDfsLoop A B C D E F )
      )
    )
  )
) $.

${
  $d A M P Q S V $.

  $( Source state carrier, moves, success predicate, and dfs parameters. $)
  ntp4vc-state-carrier-nonempty $e |- V =/= (/) $.
  ntp4vc-moves-function $e |- M e. ( ( Word V ) ^m V ) $.
  ntp4vc-success-predicate $e |- S C_ V $.
  ntp4vc-source-state $e |- A e. V $.
  ntp4vc-p-integer $e |- P e. ZZ $.
  ntp4vc-m-integer $e |- Q e. ZZ $.

  $( Source preconditions fact0 and fact1. $)
  ntp4vc-fact0 $e |- 0 <_ P $.
  ntp4vc-fact1 $e |- P <_ ( Q + 1 ) $.

  ntp4vc-pearl-search-dfs-vc $a |-
    ( NTP4VCDfsCase V M S A P Q ) $.
$}
