$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc: the
  verification condition for removing duplicate array elements with a mutable
  finite set, including both loop invariants and cardinal updates. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited element carrier, D is its chosen default
  element, S is the arbitrary inhabited mutable-set state carrier, and T maps
  states to finite subsets of U. SetMM finite subsets give an extensional
  target-native presentation of the source FSet interface: membership is e.,
  insertion is singleton union, and cardinality is #.

  Finite arrays are represented exactly by Word U. NTP4VCToNat, NTP4VCAt,
  NTP4VCSet, and NTP4VCFunUpdate reproduce the source Int.toNat, totalized
  list lookup, List.set, and total function update. The remaining definitions
  expand the complete verification condition, preserving both loop
  obligations, every invariant, the mutable-set transitions, array-update
  law, proposition-valued branches, and final no-duplicates and occurrence
  equivalence postcondition.

  The final $a declaration is Metamath's native unproved statement encoding.
  Every preceding $a is syntax or a faithful definition needed to state it;
  this database has no $p proof.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCFunUpdate
  NTP4VCAppears NTP4VCNoDupPrefix
  NTP4VCAppearsSet NTP4VCSetAppears
  NTP4VCIndexBounds NTP4VCCounterInvariant
  NTP4VCSecondInvariant NTP4VCPostcondition
  NTP4VCAddSpec NTP4VCFirstAddTransition
  NTP4VCInitialOutput NTP4VCUpdateLaw
  NTP4VCUpdatedOutputConclusion NTP4VCNonMemberBranch
  NTP4VCSecondStep NTP4VCSecondLoopObligation
  NTP4VCInitialSecondInvariant NTP4VCSecondLoopVC
  NTP4VCAllocateAndRunSecondLoop NTP4VCFirstLoopObligation
  NTP4VCRemoveDuplicateBody
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-fun-update-syntax
  $a class ( NTP4VCFunUpdate A B C D ) $.

ntp4vc-appears-syntax
  $a wff ( NTP4VCAppears A B C D E ) $.
ntp4vc-no-dup-prefix-syntax
  $a wff ( NTP4VCNoDupPrefix A B C D ) $.
ntp4vc-appears-set-syntax
  $a wff ( NTP4VCAppearsSet A B C D E F ) $.
ntp4vc-set-appears-syntax
  $a wff ( NTP4VCSetAppears A B C D E F ) $.
ntp4vc-index-bounds-syntax
  $a wff ( NTP4VCIndexBounds A B ) $.
ntp4vc-counter-invariant-syntax
  $a wff ( NTP4VCCounterInvariant A B C D ) $.
ntp4vc-second-invariant-syntax
  $a wff ( NTP4VCSecondInvariant A B C D E F G H I ) $.
ntp4vc-postcondition-syntax
  $a wff ( NTP4VCPostcondition A B C D ) $.
ntp4vc-add-spec-syntax
  $a wff ( NTP4VCAddSpec A B C D ) $.
ntp4vc-first-add-transition-syntax
  $a wff ( NTP4VCFirstAddTransition A B C D E F G ) $.
ntp4vc-initial-output-syntax
  $a wff ( NTP4VCInitialOutput A B C D E F ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D E ) $.
ntp4vc-updated-output-conclusion-syntax
  $a wff (
    NTP4VCUpdatedOutputConclusion A B C D E F G H I J
  ) $.
ntp4vc-non-member-branch-syntax
  $a wff ( NTP4VCNonMemberBranch A B C D E F G H I J ) $.
ntp4vc-second-step-syntax
  $a wff ( NTP4VCSecondStep A B C D E F G H I J ) $.
ntp4vc-second-loop-obligation-syntax
  $a wff ( NTP4VCSecondLoopObligation A B C D E F G H ) $.
ntp4vc-initial-second-invariant-syntax
  $a wff ( NTP4VCInitialSecondInvariant A B C D E F G ) $.
ntp4vc-second-loop-vc-syntax
  $a wff ( NTP4VCSecondLoopVC A B C D E F G H ) $.
ntp4vc-allocate-second-loop-syntax
  $a wff ( NTP4VCAllocateAndRunSecondLoop A B C D E F ) $.
ntp4vc-first-loop-obligation-syntax
  $a wff ( NTP4VCFirstLoopObligation A B C D E F ) $.
ntp4vc-remove-duplicate-body-syntax
  $a wff ( NTP4VCRemoveDuplicateBody A B C D E F ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-fun-update-definition $a |- (
    NTP4VCFunUpdate A B C D
  ) = (
    k e. B |->
      if (
        k = C ,
        D ,
        ( A ` k )
      )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-appears-definition $a |- (
    NTP4VCAppears A B C D E
  ) <-> E. i e. ZZ (
    (
      0 <_ i
      /\
      i < C
    )
    /\
    ( NTP4VCAt A i D ) = B
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-no-dup-prefix-definition $a |- (
    NTP4VCNoDupPrefix A B C D
  ) <-> A. i e. ZZ (
    (
      0 <_ i
      /\
      i < B
    ) -> -.
      ( NTP4VCAppears A ( NTP4VCAt A i C ) i C D )
  ) $.
$}

${
  $d x A B C D E F $.

  ntp4vc-appears-set-definition $a |- (
    NTP4VCAppearsSet A B C D E F
  ) <-> A. x e. F (
    ( NTP4VCAppears A x B E F )
    <->
    x e. ( D ` C )
  ) $.
$}

${
  $d x A B C D E F $.

  ntp4vc-set-appears-definition $a |- (
    NTP4VCSetAppears A B C D E F
  ) <-> A. x e. F (
    x e. ( D ` A )
    <->
    ( NTP4VCAppears B x C E F )
  ) $.
$}

ntp4vc-index-bounds-definition $a |- (
  NTP4VCIndexBounds A B
) <-> (
  0 <_ B
  /\
  B < ( # ` A )
) $.

ntp4vc-counter-invariant-definition $a |- (
  NTP4VCCounterInvariant A B C D
) <-> (
  0 <_ B
  /\
  (
    B = ( # ` ( D ` C ) )
    /\
    ( # ` ( D ` C ) ) <_ ( # ` A )
  )
) $.

ntp4vc-second-invariant-definition $a |- (
  NTP4VCSecondInvariant A B C D E F G H I
) <-> (
  ( NTP4VCAppearsSet A F E G H I )
  /\
  (
    ( NTP4VCSetAppears E C D G H I )
    /\
    (
      ( NTP4VCNoDupPrefix C D H I )
      /\
      (
        ( NTP4VCCounterInvariant C D E G )
        /\
        ( G ` E ) C_ ( G ` B )
      )
    )
  )
) $.

${
  $d x A B C D $.

  ntp4vc-postcondition-definition $a |- (
    NTP4VCPostcondition A B C D
  ) <-> (
    ( NTP4VCNoDupPrefix B ( # ` B ) C D )
    /\
    A. x e. D (
      ( NTP4VCAppears A x ( # ` A ) C D )
      <->
      ( NTP4VCAppears B x ( # ` B ) C D )
    )
  ) $.
$}

ntp4vc-add-spec-definition $a |- (
  NTP4VCAddSpec A B C D
) <-> (
  ( D ` C ) = ( { B } u. ( D ` A ) )
  /\
  (
    (
      B e. ( D ` A )
      ->
      ( # ` ( D ` C ) ) = ( # ` ( D ` A ) )
    )
    /\
    (
      -. B e. ( D ` A )
      ->
      ( # ` ( D ` C ) ) = ( ( # ` ( D ` A ) ) + 1 )
    )
  )
) $.

${
  $d s A B C D E F G $.

  ntp4vc-first-add-transition-definition $a |- (
    NTP4VCFirstAddTransition A B C D E F G
  ) <-> A. s e. G (
    ( NTP4VCAddSpec C ( NTP4VCAt A B E ) s D )
    ->
    ( NTP4VCAppearsSet A ( B + 1 ) s D E F )
  ) $.
$}

${
  $d i A B C D E F $.

  ntp4vc-initial-output-definition $a |- (
    NTP4VCInitialOutput A B C D E F
  ) <-> A. i e. ZZ (
    (
      0 <_ i
      /\
      i < ( # ` ( D ` B ) )
    ) ->
    ( NTP4VCAt C i E ) = ( NTP4VCAt A 0 E )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D E
  ) <-> (
    ( # ` B ) = ( # ` A )
    /\
    (
      i e. ZZ |-> ( NTP4VCAt B i E )
    ) = (
      NTP4VCFunUpdate
        ( i e. ZZ |-> ( NTP4VCAt A i E ) )
        ZZ
        C
        D
    )
  ) $.
$}

ntp4vc-updated-output-conclusion-definition $a |- (
  NTP4VCUpdatedOutputConclusion A B C D E F G H I J
) <-> (
  ( NTP4VCIndexBounds A C )
  /\
  (
    (
      0 <_ E
      /\
      E < ( # ` D )
    )
    /\
    (
      (
        NTP4VCUpdateLaw
          D
          ( NTP4VCSet D E ( NTP4VCAt A C I ) )
          E
          ( NTP4VCAt A C I )
          I
      )
      ->
      (
        NTP4VCSecondInvariant
          A
          B
          ( NTP4VCSet D E ( NTP4VCAt A C I ) )
          ( E + 1 )
          G
          ( C + 1 )
          H
          I
          J
      )
    )
  )
) $.

${
  $d s A B C D E F G H I J $.

  ntp4vc-non-member-branch-definition $a |- (
    NTP4VCNonMemberBranch A B C D E F G H I J
  ) <-> (
    ( NTP4VCIndexBounds A C )
    /\
    A. s e. J (
      ( NTP4VCAddSpec F ( NTP4VCAt A C H ) s G )
      ->
      (
        NTP4VCUpdatedOutputConclusion
          A B C D E F s G H I
      )
    )
  ) $.
$}

ntp4vc-second-step-definition $a |- (
  NTP4VCSecondStep A B C D E F G H I J
) <-> (
  ( NTP4VCIndexBounds A C )
  /\
  (
    (
      -. ( NTP4VCAt A C H ) e. ( G ` F )
      ->
      ( NTP4VCNonMemberBranch A B C D E F G H I J )
    )
    /\
    (
      ( NTP4VCAt A C H ) e. ( G ` F )
      ->
      (
        NTP4VCSecondInvariant
          A B D E F ( C + 1 ) G H I
      )
    )
  )
) $.

${
  $d i j o s A B C D E F G H $.

  ntp4vc-second-loop-obligation-definition $a |- (
    NTP4VCSecondLoopObligation A B C D E F G H
  ) <-> A. j e. ZZ A. o e. ( Word G ) A. s e. H (
    ( # ` o ) = ( # ` C )
    ->
    (
      A. i e. ZZ (
        (
          (
            0 <_ i
            /\
            i <_ D
          )
          /\
          (
            NTP4VCSecondInvariant
              A B o j s i E F G
          )
        ) ->
        ( NTP4VCSecondStep A B i o j s E F G H )
      )
      /\
      (
        (
          NTP4VCSecondInvariant
            A B o j s ( D + 1 ) E F G
        )
        ->
        ( NTP4VCPostcondition A o F G )
      )
    )
  ) $.
$}

ntp4vc-initial-second-invariant-definition $a |- (
  NTP4VCInitialSecondInvariant A B C D E F G
) <-> (
  ( NTP4VCAppearsSet A 0 D E F G )
  /\
  (
    ( NTP4VCSetAppears D C 0 E F G )
    /\
    (
      ( NTP4VCNoDupPrefix C 0 F G )
      /\
      (
        ( NTP4VCCounterInvariant C 0 D E )
        /\
        ( E ` D ) C_ ( E ` B )
      )
    )
  )
) $.

ntp4vc-second-loop-vc-definition $a |- (
  NTP4VCSecondLoopVC A B C D E F G H
) <-> (
  (
    0 <_ ( ( ( # ` A ) - 1 ) + 1 )
    ->
    (
      ( NTP4VCInitialSecondInvariant A B C D E F G )
      /\
      (
        NTP4VCSecondLoopObligation
          A B C ( ( # ` A ) - 1 ) E F G H
      )
    )
  )
  /\
  (
    ( ( ( # ` A ) - 1 ) + 1 ) < 0
    ->
    ( NTP4VCPostcondition A C F G )
  )
) $.

${
  $d o s A B C D E F $.

  ntp4vc-allocate-second-loop-definition $a |- (
    NTP4VCAllocateAndRunSecondLoop A B C D E F
  ) <-> (
    0 <_ ( # ` ( C ` B ) )
    /\
    A. o e. ( Word E ) (
      (
        ( NTP4VCInitialOutput A B o C D E )
        /\
        ( # ` o ) = ( # ` ( C ` B ) )
      ) ->
      A. s e. F (
        ( C ` s ) = (/) ->
        ( NTP4VCSecondLoopVC A B o s C D E F )
      )
    )
  ) $.
$}

${
  $d i s A B C D E F $.

  ntp4vc-first-loop-obligation-definition $a |- (
    NTP4VCFirstLoopObligation A B C D E F
  ) <-> A. s e. F (
    A. i e. ZZ (
      (
        (
          0 <_ i
          /\
          i <_ B
        )
        /\
        ( NTP4VCAppearsSet A i s C D E )
      ) ->
      (
        ( NTP4VCIndexBounds A i )
        /\
        ( NTP4VCFirstAddTransition A i s C D E F )
      )
    )
    /\
    (
      ( NTP4VCAppearsSet A ( B + 1 ) s C D E )
      ->
      (
        ( NTP4VCIndexBounds A 0 )
        /\
        ( NTP4VCAllocateAndRunSecondLoop A s C D E F )
      )
    )
  ) $.
$}

ntp4vc-remove-duplicate-body-definition $a |- (
  NTP4VCRemoveDuplicateBody A B C D E F
) <-> (
  (
    0 <_ ( ( ( # ` A ) - 1 ) + 1 )
    ->
    (
      ( NTP4VCAppearsSet A 0 B C D E )
      /\
      (
        NTP4VCFirstLoopObligation
          A ( ( # ` A ) - 1 ) C D E F
      )
    )
  )
  /\
  (
    ( ( ( # ` A ) - 1 ) + 1 ) < 0
    ->
    (
      ( NTP4VCIndexBounds A 0 )
      /\
      ( NTP4VCAllocateAndRunSecondLoop A B C D E F )
    )
  )
) $.

${
  $d x A B D H S T U $.

  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-state-carrier-nonempty $e |- S =/= (/) $.
  ntp4vc-default-element $e |- D e. U $.
  ntp4vc-to-fset-function $e |- T e. ( ( ~P U ) ^m S ) $.
  ntp4vc-to-fset-finite $e |- A. x e. S ( T ` x ) e. Fin $.
  ntp4vc-choose-function $e |- H e. ( U ^m S ) $.
  ntp4vc-choose-spec $e |- A. x e. S (
    ( T ` x ) =/= (/) ->
    ( H ` x ) e. ( T ` x )
  ) $.
  ntp4vc-input-type $e |- A e. ( Word U ) $.
  ntp4vc-initial-state-type $e |- B e. S $.
  ntp4vc-fact0 $e |- 1 <_ ( # ` A ) $.
  ntp4vc-fact1 $e |- ( T ` B ) = (/) $.
  ntp4vc-fact2 $e |- ( # ` ( T ` B ) ) = 0 $.

  ntp4vc-remove-duplicate-vc $a |- (
    NTP4VCRemoveDuplicateBody A B T D U S
  ) $.
$}
