$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/linked_list_rev_Termination_list_reversalqtvc: the linked-list
  reversal termination verification condition initializes and preserves
  finite-memory, indexing, reachability, and lexicographic loop-variant
  obligations through pointer and index-map updates. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  C is an arbitrary nonempty carrier for the source type loc, B is null, and
  A is the total next-location function mem1. The one-field source mem record
  is identified definitionally with its next function. All source integer
  variables retain the full unbounded carrier ZZ, and all location and
  integer maps retain their full total-function spaces.

  NTP4VCValidCells, NTP4VCInsideMemory, and NTP4VCFiniteMemory directly
  expand the source definitions. NTP4VCSeen is the cardinality of precisely
  those positions in the source half-open integer interval where the index is
  positive; this is the unique value specified by fc'def and the imported
  NumOf recursion. NTP4VCO is exactly o1, and NTP4VCUpdate is full-domain
  pointwise function update.

  The remaining named predicates only factor the nested invariant, branch,
  and post-state formulas. Each proposition-valued source conditional is
  expanded into its two exhaustive guarded branches. Let-bound values are
  substituted definitionally, internal loop variables remain universally
  quantified at their source scopes, and the repeated non-null conjuncts and
  both lexicographic disjuncts are retained verbatim in logical form. Every
  auxiliary $a declaration below is syntax or an explicit faithful
  definition. The final $a declaration is Metamath's native unproved
  statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCUpdate NTP4VCO NTP4VCValidCells NTP4VCInsideMemory
  NTP4VCFiniteMemory NTP4VCSeen NTP4VCBounds NTP4VCZeroSpec
  NTP4VCChain NTP4VCInvariant NTP4VCThenPost NTP4VCThenBranch
  NTP4VCElseBranch NTP4VCStepBranch NTP4VCLoop NTP4VCInitial
  NTP4VCListReversalVC
$.

ntp4vc-update-syntax
  $a class ( NTP4VCUpdate A B C D ) $.
ntp4vc-o-syntax
  $a class ( NTP4VCO A B ) $.
ntp4vc-valid-cells-syntax
  $a wff ( NTP4VCValidCells A B C ) $.
ntp4vc-inside-memory-syntax
  $a wff ( NTP4VCInsideMemory A B C D ) $.
ntp4vc-finite-memory-syntax
  $a wff ( NTP4VCFiniteMemory A B C D ) $.
ntp4vc-seen-syntax
  $a class ( NTP4VCSeen A B C D ) $.
ntp4vc-bounds-syntax
  $a wff ( NTP4VCBounds A B C D ) $.
ntp4vc-zero-spec-syntax
  $a wff ( NTP4VCZeroSpec A B C ) $.
ntp4vc-chain-syntax
  $a wff ( NTP4VCChain A B C D E F ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G H ) $.
ntp4vc-then-post-syntax
  $a wff ( NTP4VCThenPost A B C D E F G H ) $.
ntp4vc-then-branch-syntax
  $a wff ( NTP4VCThenBranch A B C D E F G H ) $.
ntp4vc-else-branch-syntax
  $a wff ( NTP4VCElseBranch A B C D E F G H ) $.
ntp4vc-step-branch-syntax
  $a wff ( NTP4VCStepBranch A B C D E F G H ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D E F ) $.
ntp4vc-list-reversal-vc-syntax
  $a wff ( NTP4VCListReversalVC A B C ) $.

${
  $d x A B C D $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D
  ) = (
    x e. D |->
      if ( x = B , C , ( A ` x ) )
  ) $.
$}

${
  $d x A B $.

  ntp4vc-o-definition $a |- (
    NTP4VCO A B
  ) = (
    x e. B |->
      if ( x = A , 0 , ( -u 1 ) )
  ) $.
$}

${
  $d i j A B C $.

  ntp4vc-valid-cells-definition $a |- (
    NTP4VCValidCells A B C
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < B
          )
          ->
          ( A ` i ) =/= C
        )
    )
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < B
            )
            /\
            (
              (
                0 <_ j
                /\
                j < B
              )
              /\
              i =/= j
            )
          )
          ->
          ( A ` i ) =/= ( A ` j )
        )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-inside-memory-definition $a |- (
    NTP4VCInsideMemory A B C D
  ) <-> (
    C = D
    \/
    E. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        /\
        C = ( A ` i )
      )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-finite-memory-definition $a |- (
    NTP4VCFiniteMemory A B C D
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        (
          NTP4VCInsideMemory
            B C ( A ` ( B ` i ) ) D
        )
      )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-seen-definition $a |- (
    NTP4VCSeen A B C D
  ) = (
    # `
    { i e. ( C ..^ D ) |
      0 < ( B ` ( A ` i ) ) }
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-bounds-definition $a |- (
    NTP4VCBounds A B C D
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          ( -u 1 ) <_ ( C ` ( A ` i ) )
          /\
          ( C ` ( A ` i ) ) <_ D
        )
      )
  ) $.
$}

${
  $d p A B C $.

  ntp4vc-zero-spec-definition $a |- (
    NTP4VCZeroSpec A B C
  ) <-> (
    A. p e. C
      (
        ( A ` p ) = 0
        <->
        p = B
      )
  ) $.
$}

${
  $d i A B C D E F $.

  ntp4vc-chain-definition $a |- (
    NTP4VCChain A B C D E F
  ) <-> (
    (
      ( C ` E ) = ( -u 1 )
      /\
      (
        ( C ` D ) = ( NTP4VCSeen A C 0 B )
        /\
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < B
            )
            ->
            (
              0 < ( C ` ( A ` i ) )
              ->
              (
                C ` ( F ` ( A ` i ) )
              )
              =
              (
                ( C ` ( A ` i ) ) - 1
              )
            )
          )
      )
    )
    \/
    (
      ( C ` E ) =/= ( -u 1 )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < B
          )
          ->
          (
            (
              0 < ( C ` ( A ` i ) )
              /\
              ( C ` ( A ` i ) ) <_ ( C ` E )
            )
            ->
            (
              C ` ( F ` ( A ` i ) )
            )
            =
            (
              ( C ` ( A ` i ) ) - 1
            )
          )
        )
    )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  NTP4VCInvariant A B C D E F G H
) <-> (
  ( NTP4VCInsideMemory A B E G )
  /\
  (
    ( NTP4VCInsideMemory A B D G )
    /\
    (
      ( NTP4VCFiniteMemory F A B G )
      /\
      (
        0 <_ ( NTP4VCSeen A C 0 B )
        /\
        (
          (
            NTP4VCBounds
              A B C ( NTP4VCSeen A C 0 B )
          )
          /\
          (
            ( NTP4VCZeroSpec C G H )
            /\
            ( NTP4VCChain A B C D E F )
          )
        )
      )
    )
  )
) $.

ntp4vc-then-post-definition $a |- (
  NTP4VCThenPost A B C D E F G H
) <-> (
  E =/= G
  /\
  (
    E =/= G
    /\
    (
      (
        (
          0 <_ ( B - ( NTP4VCSeen A C 0 B ) )
          /\
          (
            B - ( ( NTP4VCSeen A C 0 B ) + 1 )
          )
          <
          (
            B - ( NTP4VCSeen A C 0 B )
          )
        )
        \/
        (
          (
            B - ( NTP4VCSeen A C 0 B )
          )
          =
          (
            B - ( ( NTP4VCSeen A C 0 B ) + 1 )
          )
          /\
          (
            0 <_ ( 1 + ( C ` E ) )
            /\
            (
              1
              +
              (
                (
                  NTP4VCUpdate
                    C E
                    ( ( NTP4VCSeen A C 0 B ) + 1 )
                    H
                )
                ` ( F ` E )
              )
            )
            <
            ( 1 + ( C ` E ) )
          )
        )
      )
      /\
      (
        ( NTP4VCInsideMemory A B ( F ` E ) G )
        /\
        (
          ( NTP4VCInsideMemory A B E G )
          /\
          (
            (
              NTP4VCFiniteMemory
                ( NTP4VCUpdate F E D H ) A B G
            )
            /\
            (
              (
                (
                  ( NTP4VCSeen A C 0 B ) + 1
                )
                =
                (
                  NTP4VCSeen
                    A
                    (
                      NTP4VCUpdate
                        C E
                        ( ( NTP4VCSeen A C 0 B ) + 1 )
                        H
                    )
                    0 B
                )
                /\
                0
                <_
                (
                  NTP4VCSeen
                    A
                    (
                      NTP4VCUpdate
                        C E
                        ( ( NTP4VCSeen A C 0 B ) + 1 )
                        H
                    )
                    0 B
                )
              )
              /\
              (
                (
                  NTP4VCBounds
                    A B
                    (
                      NTP4VCUpdate
                        C E
                        ( ( NTP4VCSeen A C 0 B ) + 1 )
                        H
                    )
                    ( ( NTP4VCSeen A C 0 B ) + 1 )
                )
                /\
                (
                  (
                    NTP4VCZeroSpec
                      (
                        NTP4VCUpdate
                          C E
                          ( ( NTP4VCSeen A C 0 B ) + 1 )
                          H
                      )
                      G H
                  )
                  /\
                  (
                    NTP4VCChain
                      A B
                      (
                        NTP4VCUpdate
                          C E
                          ( ( NTP4VCSeen A C 0 B ) + 1 )
                          H
                      )
                      E
                      ( F ` E )
                      ( NTP4VCUpdate F E D H )
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

ntp4vc-then-branch-definition $a |- (
  NTP4VCThenBranch A B C D E F G H
) <-> (
  (
    ( NTP4VCValidCells A B G )
    /\
    (
      ( NTP4VCInsideMemory A B E G )
      /\
      (
        E =/= G
        /\
        (
          ( C ` E ) = ( -u 1 )
          /\
          0 <_ ( NTP4VCSeen A C 0 B )
        )
      )
    )
  )
  /\
  (
    (
      NTP4VCSeen
        A
        (
          NTP4VCUpdate
            C E
            ( ( NTP4VCSeen A C 0 B ) + 1 )
            H
        )
        0 B
    )
    =
    ( 1 + ( NTP4VCSeen A C 0 B ) )
    ->
    ( NTP4VCThenPost A B C D E F G H )
  )
) $.

ntp4vc-else-branch-definition $a |- (
  NTP4VCElseBranch A B C D E F G H
) <-> (
  E =/= G
  /\
  (
    E =/= G
    /\
    (
      (
        (
          0 <_ ( B - ( NTP4VCSeen A C 0 B ) )
          /\
          (
            B - ( NTP4VCSeen A C 0 B )
          )
          <
          (
            B - ( NTP4VCSeen A C 0 B )
          )
        )
        \/
        (
          0 <_ ( 1 + ( C ` E ) )
          /\
          (
            1 + ( C ` ( F ` E ) )
          )
          <
          ( 1 + ( C ` E ) )
        )
      )
      /\
      (
        ( NTP4VCInsideMemory A B ( F ` E ) G )
        /\
        (
          ( NTP4VCInsideMemory A B E G )
          /\
          (
            (
              NTP4VCFiniteMemory
                ( NTP4VCUpdate F E D H ) A B G
            )
            /\
            (
              0 <_ ( NTP4VCSeen A C 0 B )
              /\
              (
                (
                  NTP4VCBounds
                    A B C ( NTP4VCSeen A C 0 B )
                )
                /\
                (
                  ( NTP4VCZeroSpec C G H )
                  /\
                  (
                    NTP4VCChain
                      A B C E ( F ` E )
                      ( NTP4VCUpdate F E D H )
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

ntp4vc-step-branch-definition $a |- (
  NTP4VCStepBranch A B C D E F G H
) <-> (
  (
    ( C ` E ) = ( -u 1 )
    /\
    ( NTP4VCThenBranch A B C D E F G H )
  )
  \/
  (
    ( C ` E ) =/= ( -u 1 )
    /\
    ( NTP4VCElseBranch A B C D E F G H )
  )
) $.

${
  $d q r l m A B C D $.

  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D
  ) <-> (
    A. q e. ( ZZ ^m D )
      A. r e. D
        A. l e. D
          A. m e. ( D ^m D )
            (
              ( NTP4VCInvariant A B q r l m C D )
              ->
              (
                l =/= C
                ->
                ( NTP4VCStepBranch A B q r l m C D )
              )
            )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B C D E F
) <-> (
  ( NTP4VCInsideMemory B C D E )
  /\
  (
    ( NTP4VCInsideMemory B C E E )
    /\
    (
      ( NTP4VCFiniteMemory A B C E )
      /\
      (
        (
          0 = ( NTP4VCSeen B ( NTP4VCO E F ) 0 C )
          /\
          0 <_ ( NTP4VCSeen B ( NTP4VCO E F ) 0 C )
        )
        /\
        (
          (
            NTP4VCBounds B C ( NTP4VCO E F ) 0
          )
          /\
          (
            ( NTP4VCZeroSpec ( NTP4VCO E F ) E F )
            /\
            (
              NTP4VCChain
                B C ( NTP4VCO E F ) E D A
            )
          )
        )
      )
    )
  )
) $.

${
  $d s n l A B C $.

  ntp4vc-list-reversal-vc-definition $a |- (
    NTP4VCListReversalVC A B C
  ) <-> (
    A. s e. ( C ^m ZZ )
      A. n e. ZZ
        A. l e. C
          (
            (
              0 <_ n
              /\
              (
                ( NTP4VCValidCells s n B )
                /\
                (
                  ( NTP4VCFiniteMemory A s n B )
                  /\
                  ( NTP4VCInsideMemory s n l B )
                )
              )
            )
            ->
            (
              ( NTP4VCInitial A s n l B C )
              /\
              ( NTP4VCLoop s n B C )
            )
          )
  ) $.
$}

${
  $d A B C $.

  $( Source declarations: C=loc, A=mem1, and B=null. $)

  ntp4vc-location-carrier-nonempty $e |- C =/= (/) $.
  ntp4vc-next-function $e |- A e. ( C ^m C ) $.
  ntp4vc-null-location $e |- B e. C $.

  ntp4vc-pearl-linked-list-rev-termination-list-reversal-vc
    $a |- ( NTP4VCListReversalVC A B C ) $.
$}
