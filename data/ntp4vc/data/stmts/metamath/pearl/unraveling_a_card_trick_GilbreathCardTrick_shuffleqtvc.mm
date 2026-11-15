$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc
  (ntp4vc__metamath__pearl/unraveling_a_card_trick_GilbreathCardTrick_shuffleqtvc):
  the Gilbreath card-trick shuffle-loop verification condition preserves the
  riffle-shuffle invariant while popping either nonempty input stack and
  establishes the final shuffle when both inputs are empty. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  source type of arbitrary finite zero-based integer lists. As in the
  established Metamath encoding of the companion card_trick VC, a Why3
  Stack.t int is represented extensionally by its complete elts word, and
  Stack.length is the word length. Thus no finite list or stack state is
  omitted.

  NTP4VCReverse is exact finite-list reversal. NTP4VCShuffle is the least
  ternary relation on integer words containing the two empty-side cases and
  closed under taking the next card from either input, exactly matching the
  four constructors of the source inductive predicate.

  NTP4VCState is the displayed three-part loop invariant. NTP4VCO1Spec and
  NTP4VCO2Spec expand the source Boolean-valued conditionals over the
  two-element carrier { 0, 1 }, with 0=false and 1=true. The two branch
  predicates retain every source universal quantifier over head values,
  successor stacks, popped tails, and updated shuffle results. A nonempty
  list match is represented equivalently by exact singleton-cons
  decomposition. Proposition-valued conditionals are expanded into their
  exhaustive guarded branches.

  Expanding the definitions gives the original Why3 verification condition
  and the agreeing Lean, Rocq, and Isabelle exports. Every auxiliary $a below
  is syntax or a faithful definitional abbreviation. The final $a declaration
  is Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCReverse NTP4VCShuffle NTP4VCState NTP4VCHead
  NTP4VCO1Spec NTP4VCO2Spec NTP4VCABranch NTP4VCBBranch
  NTP4VCStep NTP4VCTerminal NTP4VCO1Flow NTP4VCContinuation
  NTP4VCShuffleVC
$.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-shuffle-syntax
  $a wff ( NTP4VCShuffle A B C ) $.
ntp4vc-state-syntax
  $a wff ( NTP4VCState A B C D E F G ) $.
ntp4vc-head-syntax
  $a wff ( NTP4VCHead A B ) $.
ntp4vc-o1-spec-syntax
  $a wff ( NTP4VCO1Spec A B C ) $.
ntp4vc-o2-spec-syntax
  $a wff ( NTP4VCO2Spec A B C ) $.
ntp4vc-a-branch-syntax
  $a wff ( NTP4VCABranch A B C D E F G ) $.
ntp4vc-b-branch-syntax
  $a wff ( NTP4VCBBranch A B C D E F G ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H ) $.
ntp4vc-terminal-syntax
  $a wff ( NTP4VCTerminal A B C D E ) $.
ntp4vc-o1-flow-syntax
  $a wff ( NTP4VCO1Flow A B C D E F G H ) $.
ntp4vc-continuation-syntax
  $a wff ( NTP4VCContinuation A B ) $.
ntp4vc-shuffle-vc-syntax
  $a wff ( NTP4VCShuffleVC A B C D E ) $.

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d a b c l r x A B C $.

  ntp4vc-shuffle-definition $a |- (
    NTP4VCShuffle A B C
  ) <-> (
    A. r
      (
        (
          (
            A. l e. Word ZZ
              <. <. l , (/) >. , l >. e. r
            /\
            A. l e. Word ZZ
              <. <. (/) , l >. , l >. e. r
          )
          /\
          (
            A. x e. ZZ
              A. a e. Word ZZ A. b e. Word ZZ A. c e. Word ZZ
                (
                  <. <. a , b >. , c >. e. r
                  ->
                  <.
                    <. ( <" x "> ++ a ) , b >. ,
                    ( <" x "> ++ c )
                  >. e. r
                )
            /\
            A. x e. ZZ
              A. a e. Word ZZ A. b e. Word ZZ A. c e. Word ZZ
                (
                  <. <. a , b >. , c >. e. r
                  ->
                  <.
                    <. a , ( <" x "> ++ b ) >. ,
                    ( <" x "> ++ c )
                  >. e. r
                )
          )
        )
        ->
        <. <. A , B >. , C >. e. r
      )
  ) $.
$}

ntp4vc-state-definition $a |- (
  NTP4VCState A B C D E F G
) <-> (
  ( NTP4VCReverse A ) = ( ( NTP4VCReverse F ) ++ C )
  /\
  (
    ( NTP4VCReverse B ) = ( ( NTP4VCReverse G ) ++ D )
    /\
    ( NTP4VCShuffle C D E )
  )
) $.

${
  $d t A B $.

  ntp4vc-head-definition $a |- (
    NTP4VCHead A B
  ) <-> (
    E. t e. Word ZZ
      A = ( <" B "> ++ t )
  ) $.
$}

ntp4vc-o1-spec-definition $a |- (
  NTP4VCO1Spec A B C
) <-> (
  (
    A = (/)
    /\
    (
      (
        B = (/)
        /\
        C = 1
      )
      \/
      (
        B =/= (/)
        /\
        C = 0
      )
    )
  )
  \/
  (
    A =/= (/)
    /\
    C = 0
  )
) $.

ntp4vc-o2-spec-definition $a |- (
  NTP4VCO2Spec A B C
) <-> (
  (
    A =/= (/)
    /\
    (
      B = (/)
      ->
      C = 1
    )
  )
  \/
  (
    A = (/)
    /\
    C = 0
  )
) $.

${
  $d p q r x y A B C D E F G $.

  ntp4vc-a-branch-definition $a |- (
    NTP4VCABranch A B C D E F G
  ) <-> (
    F =/= (/)
    /\
    A. x e. ZZ
      (
        ( NTP4VCHead F x )
        ->
        A. p e. Word ZZ
          (
            p = ( <" x "> ++ C )
            ->
            (
              F =/= (/)
              /\
              A. q e. Word ZZ A. y e. ZZ
                (
                  F = ( <" y "> ++ q )
                  ->
                  A. r e. Word ZZ
                    (
                      r = ( <" y "> ++ E )
                      ->
                      (
                        (
                          0 <_ ( ( # ` F ) + ( # ` G ) )
                          /\
                          (
                            ( ( # ` q ) + ( # ` G ) )
                            <
                            ( ( # ` F ) + ( # ` G ) )
                          )
                        )
                        /\
                        ( NTP4VCState A B p D r q G )
                      )
                    )
                )
            )
          )
      )
  ) $.
$}

${
  $d p q r x y A B C D E F G $.

  ntp4vc-b-branch-definition $a |- (
    NTP4VCBBranch A B C D E F G
  ) <-> (
    G =/= (/)
    /\
    A. x e. ZZ
      (
        ( NTP4VCHead G x )
        ->
        A. p e. Word ZZ
          (
            p = ( <" x "> ++ D )
            ->
            (
              G =/= (/)
              /\
              A. q e. Word ZZ A. y e. ZZ
                (
                  G = ( <" y "> ++ q )
                  ->
                  A. r e. Word ZZ
                    (
                      r = ( <" y "> ++ E )
                      ->
                      (
                        (
                          0 <_ ( ( # ` F ) + ( # ` G ) )
                          /\
                          (
                            ( ( # ` F ) + ( # ` q ) )
                            <
                            ( ( # ` F ) + ( # ` G ) )
                          )
                        )
                        /\
                        ( NTP4VCState A B C p r F q )
                      )
                    )
                )
            )
          )
      )
  ) $.
$}

ntp4vc-step-definition $a |- (
  NTP4VCStep A B C D E F G H
) <-> (
  (
    H = 1
    /\
    ( NTP4VCABranch A B C D E F G )
  )
  \/
  (
    H =/= 1
    /\
    ( NTP4VCBBranch A B C D E F G )
  )
) $.

ntp4vc-terminal-definition $a |- (
  NTP4VCTerminal A B C D E
) <-> (
  D = (/)
  /\
  (
    E = (/)
    /\
    (
      NTP4VCShuffle
        ( NTP4VCReverse A )
        ( NTP4VCReverse B )
        C
    )
  )
) $.

${
  $d u A B C D E F G H $.

  ntp4vc-o1-flow-definition $a |- (
    NTP4VCO1Flow A B C D E F G H
  ) <-> (
    (
      H =/= 1
      /\
      A. u e. { 0 , 1 }
        (
          ( NTP4VCO2Spec F G u )
          ->
          ( NTP4VCStep A B C D E F G u )
        )
    )
    \/
    (
      H = 1
      /\
      ( NTP4VCTerminal A B E F G )
    )
  ) $.
$}

${
  $d p q r s t u A B $.

  ntp4vc-continuation-definition $a |- (
    NTP4VCContinuation A B
  ) <-> (
    A. p e. Word ZZ A. q e. Word ZZ A. r e. Word ZZ
      A. s e. Word ZZ A. t e. Word ZZ
        (
          ( NTP4VCState A B q p r t s )
          ->
          A. u e. { 0 , 1 }
            (
              ( NTP4VCO1Spec t s u )
              ->
              ( NTP4VCO1Flow A B q p r t s u )
            )
        )
  ) $.
$}

ntp4vc-shuffle-vc-definition $a |- (
  NTP4VCShuffleVC A B C D E
) <-> (
  ( NTP4VCState D E B C A D E )
  /\
  ( NTP4VCContinuation D E )
) $.

${
  $d a b c l p q r s t u x y
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameters c, a', b', a, and b. $)
  ntp4vc-c-stack $e |- A e. Word ZZ $.
  ntp4vc-a-prime-stack $e |- B e. Word ZZ $.
  ntp4vc-b-prime-stack $e |- C e. Word ZZ $.
  ntp4vc-a-stack $e |- D e. Word ZZ $.
  ntp4vc-b-stack $e |- E e. Word ZZ $.

  $( Source assumptions fact0--fact2. $)
  ntp4vc-fact0 $e |- A = (/) $.
  ntp4vc-fact1 $e |- B = (/) $.
  ntp4vc-fact2 $e |- C = (/) $.

  ntp4vc-pearl-unraveling-a-card-trick-gilbreath-card-trick-shuffle-vc
    $a |- ( NTP4VCShuffleVC A B C D E ) $.
$}
