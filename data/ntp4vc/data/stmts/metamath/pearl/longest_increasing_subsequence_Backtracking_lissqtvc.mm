$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/longest_increasing_subsequence_Backtracking_lissqtvc: the
  backtracking longest-increasing-subsequence verification condition
  initializes and preserves the inner and outer maximality invariants and
  concludes that the selected integer-index list is a longest increasing
  subsequence of an arbitrary element list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier elt, R is its strict total
  order, and D is the source default inhabitant used by totalized lookup.
  SetMM words over U and ZZ are exactly arbitrary finite source lists.
  NTP4VCToNat, NTP4VCAtZ, and NTP4VCAtU reproduce Int.toNat and both
  totalized list lookups. NTP4VCIss and NTP4VCLiss directly expand the source
  increasing-subsequence and longest-increasing-subsequence definitions.

  The remaining named predicates factor the original nested verification
  condition. Proposition-valued conditionals are represented by exhaustive
  guarded disjunctions, and source let-bindings are substituted by their
  defining expressions. Expanding the biconditional definitions recovers
  every integer and list quantifier, loop bound, invariant, variant
  inequality, list-construction premise, and maximality conclusion. Splitting
  the inhabited strict-order context and typed list parameter into scoped
  essential hypotheses is bidirectionally equivalent to the source context.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAtZ NTP4VCAtU
  NTP4VCIss NTP4VCLiss
  NTP4VCStrongInv NTP4VCStartBest NTP4VCFinalAt
  NTP4VCGlobalBest NTP4VCGlobalInv
  NTP4VCPrependCase NTP4VCInnerChoice NTP4VCExtendCase
  NTP4VCCandidateStep NTP4VCInnerLoop NTP4VCPerStart
  NTP4VCOuterChoice NTP4VCOuterStep NTP4VCGlobalLoop
  NTP4VCGlobalPhase NTP4VCWhole
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-z-syntax $a class ( NTP4VCAtZ A B ) $.
ntp4vc-at-u-syntax $a class ( NTP4VCAtU A B C ) $.
ntp4vc-iss-syntax $a wff ( NTP4VCIss A B C D ) $.
ntp4vc-liss-syntax $a wff ( NTP4VCLiss A B C D ) $.
ntp4vc-strong-inv-syntax
  $a wff ( NTP4VCStrongInv A B C D E F G ) $.
ntp4vc-start-best-syntax
  $a wff ( NTP4VCStartBest A B C D E ) $.
ntp4vc-final-at-syntax
  $a wff ( NTP4VCFinalAt A B C D E F ) $.
ntp4vc-global-best-syntax
  $a wff ( NTP4VCGlobalBest A B C D E ) $.
ntp4vc-global-inv-syntax
  $a wff ( NTP4VCGlobalInv A B C D E F ) $.
ntp4vc-prepend-case-syntax
  $a wff ( NTP4VCPrependCase A B C D E F G H ) $.
ntp4vc-inner-choice-syntax
  $a wff ( NTP4VCInnerChoice A B C D E F G H ) $.
ntp4vc-extend-case-syntax
  $a wff ( NTP4VCExtendCase A B C D E F G ) $.
ntp4vc-candidate-step-syntax
  $a wff ( NTP4VCCandidateStep A B C D E F G ) $.
ntp4vc-inner-loop-syntax
  $a wff ( NTP4VCInnerLoop A B C D E F ) $.
ntp4vc-per-start-syntax
  $a wff ( NTP4VCPerStart A B C D ) $.
ntp4vc-outer-choice-syntax
  $a wff ( NTP4VCOuterChoice A B C D E F G ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C D E F ) $.
ntp4vc-global-loop-syntax
  $a wff ( NTP4VCGlobalLoop A B C D E ) $.
ntp4vc-global-phase-syntax
  $a wff ( NTP4VCGlobalPhase A B C ) $.
ntp4vc-whole-syntax $a wff ( NTP4VCWhole A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-z-definition $a |- (
  NTP4VCAtZ A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-at-u-definition $a |- (
  NTP4VCAtU A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d i j A B C D $.

  ntp4vc-iss-definition $a |- (
    NTP4VCIss A B C D
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` C )
          )
          ->
          (
            0 <_ ( NTP4VCAtZ C i )
            /\
            ( NTP4VCAtZ C i ) < ( # ` B )
          )
        )
    )
    /\
    A. i e. ZZ A. j e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < j
          )
          /\
          j < ( # ` C )
        )
        ->
        (
          ( NTP4VCAtZ C i ) < ( NTP4VCAtZ C j )
          /\
          <.
            ( NTP4VCAtU B ( NTP4VCAtZ C i ) D ) ,
            ( NTP4VCAtU B ( NTP4VCAtZ C j ) D )
          >. e. A
        )
      )
  ) $.
$}

${
  $d q A B C D $.

  ntp4vc-liss-definition $a |- (
    NTP4VCLiss A B C D
  ) <-> (
    ( NTP4VCIss A B C D )
    /\
    A. q e. Word ZZ
      (
        ( NTP4VCIss A B q D )
        ->
        ( # ` q ) <_ ( # ` C )
      )
  ) $.
$}

${
  $d q A B C D E F G $.

  ntp4vc-strong-inv-definition $a |- (
    NTP4VCStrongInv A B C D E F G
  ) <-> (
    (
      E = ( # ` C )
      /\
      0 < ( # ` C )
    )
    /\
    (
      ( NTP4VCAtZ C 0 ) = F
      /\
      (
        ( NTP4VCIss A B C D )
        /\
        A. q e. Word ZZ
          (
            ( NTP4VCIss A B q D )
            ->
            (
              2 <_ ( # ` q )
              ->
              (
                (
                  ( NTP4VCAtZ q 0 ) = F
                  /\
                  F < ( NTP4VCAtZ q 1 )
                )
                /\
                ( NTP4VCAtZ q 1 ) < G
                ->
                ( # ` q ) <_ ( # ` C )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d q A B C D E $.

  ntp4vc-start-best-definition $a |- (
    NTP4VCStartBest A B C D E
  ) <-> (
    0 < ( # ` C )
    /\
    (
      ( NTP4VCAtZ C 0 ) = E
      /\
      (
        ( NTP4VCIss A B C D )
        /\
        A. q e. Word ZZ
          (
            ( NTP4VCIss A B q D )
            ->
            (
              1 <_ ( # ` q )
              ->
              (
                ( NTP4VCAtZ q 0 ) = E
                ->
                ( # ` q ) <_ ( # ` C )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d q A B C D E F $.

  ntp4vc-final-at-definition $a |- (
    NTP4VCFinalAt A B C D E F
  ) <-> (
    (
      E = ( # ` C )
      /\
      0 < ( # ` C )
    )
    /\
    (
      ( NTP4VCAtZ C 0 ) = F
      /\
      (
        ( NTP4VCIss A B C D )
        /\
        A. q e. Word ZZ
          (
            ( NTP4VCIss A B q D )
            ->
            (
              1 <_ ( # ` q )
              ->
              (
                ( NTP4VCAtZ q 0 ) = F
                ->
                ( # ` q ) <_ ( # ` C )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d q A B C D E $.

  ntp4vc-global-best-definition $a |- (
    NTP4VCGlobalBest A B C D E
  ) <-> (
    ( NTP4VCIss A B C D )
    /\
    A. q e. Word ZZ
      (
        ( NTP4VCIss A B q D )
        ->
        (
          1 <_ ( # ` q )
          ->
          (
            ( NTP4VCAtZ q 0 ) < E
            ->
            ( # ` q ) <_ ( # ` C )
          )
        )
      )
  ) $.
$}

ntp4vc-global-inv-definition $a |- (
  NTP4VCGlobalInv A B C D E F
) <-> (
  E = ( # ` C )
  /\
  ( NTP4VCGlobalBest A B C D F )
) $.

${
  $d k A B C D E F G H $.

  ntp4vc-prepend-case-definition $a |- (
    NTP4VCPrependCase A B C D E F G H
  ) <-> (
    (
      (
        # ` ( <" G "> ++ D )
      )
      =
      ( 1 + ( # ` D ) )
      /\
      (
        ( NTP4VCAtZ ( <" G "> ++ D ) 0 ) = G
        /\
        A. k e. ZZ
          (
            (
              0 < k
              /\
              k <_ ( # ` D )
            )
            ->
            (
              NTP4VCAtZ ( <" G "> ++ D ) k
            )
            =
            (
              NTP4VCAtZ D ( k - 1 )
            )
          )
      )
    )
    ->
    (
      NTP4VCStrongInv
        A B ( <" G "> ++ D ) E
        ( 1 + ( # ` D ) ) G ( H + 1 )
    )
  ) $.
$}

ntp4vc-inner-choice-definition $a |- (
  NTP4VCInnerChoice A B C D E F G H
) <-> (
  (
    F < ( 1 + ( # ` D ) )
    /\
    ( NTP4VCPrependCase A B C D E F G H )
  )
  \/
  (
    -. F < ( 1 + ( # ` D ) )
    /\
    ( NTP4VCStrongInv A B C E F G ( H + 1 ) )
  )
) $.

${
  $d q A B C D E F G $.

  ntp4vc-extend-case-definition $a |- (
    NTP4VCExtendCase A B C D E F G
  ) <-> (
    (
      (
        0 <_ ( ( # ` B ) - F )
        /\
        (
          ( ( # ` B ) - G )
          <
          ( ( # ` B ) - F )
        )
      )
      /\
      (
        0 <_ G
        /\
        G < ( # ` B )
      )
    )
    /\
    A. q e. Word ZZ
      (
        ( NTP4VCStartBest A B q D G )
        ->
        ( NTP4VCInnerChoice A B C q D E F G )
      )
  ) $.
$}

ntp4vc-candidate-step-definition $a |- (
  NTP4VCCandidateStep A B C D E F G
) <-> (
  (
    <.
      ( NTP4VCAtU B F D ) ,
      ( NTP4VCAtU B G D )
    >. e. A
    /\
    ( NTP4VCExtendCase A B C D E F G )
  )
  \/
  (
    -.
    <.
      ( NTP4VCAtU B F D ) ,
      ( NTP4VCAtU B G D )
    >. e. A
    /\
    ( NTP4VCStrongInv A B C D E F ( G + 1 ) )
  )
) $.

${
  $d j A B C D E F $.

  ntp4vc-inner-loop-definition $a |- (
    NTP4VCInnerLoop A B C D E F
  ) <-> (
    (
      A. j e. ZZ
        (
          (
            (
              ( F + 1 ) <_ j
              /\
              j <_ ( ( # ` B ) - 1 )
            )
            /\
            ( NTP4VCStrongInv A B C D E F j )
          )
          ->
          ( NTP4VCCandidateStep A B C D E F j )
        )
    )
    /\
    (
      ( NTP4VCStrongInv A B C D E F ( # ` B ) )
      ->
      ( NTP4VCFinalAt A B C D E F )
    )
  ) $.
$}

${
  $d s n A B C D $.

  ntp4vc-per-start-definition $a |- (
    NTP4VCPerStart A B C D
  ) <-> (
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    ->
    (
      (
        ( # ` <" C "> ) = 1
        /\
        ( NTP4VCAtZ <" C "> 0 ) = C
      )
      ->
      (
        (
          ( C + 1 ) <_ ( ( ( # ` B ) - 1 ) + 1 )
          ->
          (
            ( NTP4VCStrongInv A B <" C "> D 1 C ( C + 1 ) )
            /\
            A. s e. Word ZZ A. n e. ZZ
              ( NTP4VCInnerLoop A B s D n C )
          )
        )
        /\
        (
          ( ( ( # ` B ) - 1 ) + 1 ) < ( C + 1 )
          ->
          ( NTP4VCFinalAt A B <" C "> D 1 C )
        )
      )
    )
  ) $.
$}

ntp4vc-outer-choice-definition $a |- (
  NTP4VCOuterChoice A B C D E F G
) <-> (
  (
    F < ( # ` D )
    /\
    ( NTP4VCGlobalBest A B D E ( G + 1 ) )
  )
  \/
  (
    -. F < ( # ` D )
    /\
    ( NTP4VCGlobalInv A B C E F ( G + 1 ) )
  )
) $.

${
  $d q A B C D E F $.

  ntp4vc-outer-step-definition $a |- (
    NTP4VCOuterStep A B C D E F
  ) <-> (
    (
      0 <_ F
      /\
      F < ( # ` B )
    )
    /\
    A. q e. Word ZZ
      (
        ( NTP4VCStartBest A B q D F )
        ->
        ( NTP4VCOuterChoice A B C q D E F )
      )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-global-loop-definition $a |- (
    NTP4VCGlobalLoop A B C D E
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i <_ ( ( # ` B ) - 1 )
            )
            /\
            ( NTP4VCGlobalInv A B C D E i )
          )
          ->
          ( NTP4VCOuterStep A B C D E i )
        )
    )
    /\
    (
      ( NTP4VCGlobalInv A B C D E ( # ` B ) )
      ->
      (
        E = ( # ` C )
        /\
        ( NTP4VCLiss A B C D )
      )
    )
  ) $.
$}

${
  $d s n A B C $.

  ntp4vc-global-phase-definition $a |- (
    NTP4VCGlobalPhase A B C
  ) <-> (
    (
      0 <_ ( ( ( # ` B ) - 1 ) + 1 )
      ->
      (
        ( NTP4VCGlobalInv A B (/) C 0 0 )
        /\
        A. s e. Word ZZ A. n e. ZZ
          ( NTP4VCGlobalLoop A B s C n )
      )
    )
    /\
    (
      ( ( ( # ` B ) - 1 ) + 1 ) < 0
      ->
      (
        0 = ( # ` (/) )
        /\
        ( NTP4VCLiss A B (/) C )
      )
    )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-whole-definition $a |- (
    NTP4VCWhole A B C
  ) <-> (
    (
      A. i e. ZZ
        ( NTP4VCPerStart A B i C )
    )
    /\
    ( NTP4VCGlobalPhase A B C )
  ) $.
$}

${
  $d x y z A B C D R U W $.

  $( Source carrier, default inhabitant, strict order, and input list. $)
  ntp4vc-default-in-carrier $e |- D e. U $.
  ntp4vc-order-relation $e |- R C_ ( U X. U ) $.
  ntp4vc-order-transitive $e |- A. x e. U A. y e. U A. z e. U
    (
      (
        <. x , y >. e. R
        /\
        <. y , z >. e. R
      )
      ->
      <. x , z >. e. R
    ) $.
  ntp4vc-order-asymmetric $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      ->
      -. <. y , x >. e. R
    ) $.
  ntp4vc-order-trichotomy $e |- A. x e. U A. y e. U
    (
      <. x , y >. e. R
      \/
      (
        <. y , x >. e. R
        \/
        x = y
      )
    ) $.
  ntp4vc-input-list $e |- W e. Word U $.

  ntp4vc-pearl-longest-increasing-subsequence-backtracking-liss-vc
    $a |- ( NTP4VCWhole R W D ) $.
$}
