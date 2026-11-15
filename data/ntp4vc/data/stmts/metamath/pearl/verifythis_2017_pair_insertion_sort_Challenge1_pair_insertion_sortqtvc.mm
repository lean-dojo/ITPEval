$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc:
  the pair-insertion-sort verification condition, including sorted-prefix and
  permutation invariants, two nested insertion loops, list updates, loop
  variants, and final sortedness. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ.
  PISToNat reproduces the source Int.toNat, PISAt is integer-indexed lookup
  with default zero outside [0, length), and PISSet reproduces List.set.
  PISSetLaw is the generated full-integer-domain Function.update equality.
  PISPerm compares every integer's occurrence count and is equivalent in both
  directions to List.Perm on finite integer words.

  The remaining predicates are biconditional factorizations of the original
  verification condition. Expanding them recovers every integer and list
  quantifier, length premise, implication, invariant, update premise, variant,
  and conclusion. Let-bound values are directly substituted. Each
  proposition-valued Boolean conditional is represented by its equivalent
  exhaustive guarded cases. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  PISToNat PISAt PISSet PISSetLaw PISPerm
  PISSortedBefore PISPrefixClosed PISCrossOrder PISSuffixOrder
  PISStrictLower PISWeakLower
  PISFirstInvariant PISSecondInvariant PISOuterNext
  PISSecondShift PISSecondFinish PISSecondStep PISSecondPhase
  PISFirstShift PISFirstFinish PISFirstStep PISFirstPhase
  PISPairCase
  PISSingleInvariant PISSingleShift PISSingleFinish
  PISSingleStep PISSinglePhase PISSingleCase
  PISOuterStep PISAllOuter PISMain
$.

pis-to-nat-syntax $a class ( PISToNat A ) $.
pis-at-syntax $a class ( PISAt A B ) $.
pis-set-syntax $a class ( PISSet A B C ) $.
pis-set-law-syntax $a wff ( PISSetLaw A B C ) $.
pis-perm-syntax $a wff ( PISPerm A B ) $.
pis-sorted-before-syntax $a wff ( PISSortedBefore A B ) $.
pis-prefix-closed-syntax $a wff ( PISPrefixClosed A B ) $.
pis-cross-order-syntax $a wff ( PISCrossOrder A B C D ) $.
pis-suffix-order-syntax $a wff ( PISSuffixOrder A B C ) $.
pis-strict-lower-syntax $a wff ( PISStrictLower A B C D ) $.
pis-weak-lower-syntax $a wff ( PISWeakLower A B C D ) $.
pis-first-invariant-syntax
  $a wff ( PISFirstInvariant A B C D E F ) $.
pis-second-invariant-syntax
  $a wff ( PISSecondInvariant A B C D E ) $.
pis-outer-next-syntax $a wff ( PISOuterNext A B C D ) $.
pis-second-shift-syntax $a wff ( PISSecondShift A B C D E ) $.
pis-second-finish-syntax
  $a wff ( PISSecondFinish A B C D E F ) $.
pis-second-step-syntax $a wff ( PISSecondStep A B C D E F ) $.
pis-second-phase-syntax
  $a wff ( PISSecondPhase A B C D E F ) $.
pis-first-shift-syntax $a wff ( PISFirstShift A B C D E F ) $.
pis-first-finish-syntax
  $a wff ( PISFirstFinish A B C D E F G ) $.
pis-first-step-syntax $a wff ( PISFirstStep A B C D E F G ) $.
pis-first-phase-syntax $a wff ( PISFirstPhase A B C D E ) $.
pis-pair-case-syntax $a wff ( PISPairCase A B C ) $.
pis-single-invariant-syntax
  $a wff ( PISSingleInvariant A B C D E ) $.
pis-single-shift-syntax $a wff ( PISSingleShift A B C D E ) $.
pis-single-finish-syntax $a wff ( PISSingleFinish A B C D ) $.
pis-single-step-syntax $a wff ( PISSingleStep A B C D E ) $.
pis-single-phase-syntax $a wff ( PISSinglePhase A B C ) $.
pis-single-case-syntax $a wff ( PISSingleCase A B C ) $.
pis-outer-step-syntax $a wff ( PISOuterStep A B C ) $.
pis-all-outer-syntax $a wff ( PISAllOuter A ) $.
pis-main-syntax $a wff ( PISMain A ) $.

pis-to-nat-definition $a |- (
  PISToNat A
) = if ( 0 <_ A , A , 0 ) $.

pis-at-definition $a |- (
  PISAt A B
) = if (
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C $.

  pis-set-definition $a |- (
    PISSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( PISToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d q A B C $.

  pis-set-law-definition $a |- (
    PISSetLaw A B C
  ) <->
  A. q e. ZZ
    (
      ( PISAt ( PISSet A B C ) q )
      =
      if (
        q = B ,
        C ,
        ( PISAt A q )
      )
    ) $.
$}

${
  $d k v A B $.

  pis-perm-definition $a |- (
    PISPerm A B
  ) <->
  (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. v e. ZZ
        (
          (
            # `
            { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
          )
          =
          (
            # `
            { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
          )
        )
    )
  ) $.
$}

${
  $d k l A B $.

  pis-sorted-before-definition $a |- (
    PISSortedBefore A B
  ) <->
  (
    A e. Word ZZ
    /\
    A. k e. ZZ
      A. l e. ZZ
        (
          (
            0 <_ k
            /\
            (
              k <_ l
              /\
              l < B
            )
          )
          ->
          ( PISAt A k ) <_ ( PISAt A l )
        )
  ) $.
$}

${
  $d k l A B $.

  pis-prefix-closed-definition $a |- (
    PISPrefixClosed A B
  ) <->
  (
    A e. Word ZZ
    /\
    A. k e. ZZ
      A. l e. ZZ
        (
          (
            0 <_ k
            /\
            (
              k <_ l
              /\
              l <_ B
            )
          )
          ->
          ( PISAt A k ) <_ ( PISAt A l )
        )
  ) $.
$}

${
  $d k l A B C D $.

  pis-cross-order-definition $a |- (
    PISCrossOrder A B C D
  ) <->
  (
    A e. Word ZZ
    /\
    A. k e. ZZ
      A. l e. ZZ
        (
          (
            0 <_ k
            /\
            k <_ B
          )
          ->
          (
            (
              C < l
              /\
              l < D
            )
            ->
            ( PISAt A k ) <_ ( PISAt A l )
          )
        )
  ) $.
$}

${
  $d k l A B C $.

  pis-suffix-order-definition $a |- (
    PISSuffixOrder A B C
  ) <->
  (
    A e. Word ZZ
    /\
    A. k e. ZZ
      A. l e. ZZ
        (
          (
            B < k
            /\
            (
              k <_ l
              /\
              l < C
            )
          )
          ->
          ( PISAt A k ) <_ ( PISAt A l )
        )
  ) $.
$}

${
  $d l A B C D $.

  pis-strict-lower-definition $a |- (
    PISStrictLower A B C D
  ) <->
  (
    A e. Word ZZ
    /\
    A. l e. ZZ
      (
        (
          C < l
          /\
          l < D
        )
        ->
        B < ( PISAt A l )
      )
  ) $.
$}

${
  $d l A B C D $.

  pis-weak-lower-definition $a |- (
    PISWeakLower A B C D
  ) <->
  (
    A e. Word ZZ
    /\
    A. l e. ZZ
      (
        (
          C < l
          /\
          l < D
        )
        ->
        B <_ ( PISAt A l )
      )
  ) $.
$}

$( A=original, B=current, C=i, D=j, E=larger, F=smaller. $)
pis-first-invariant-definition $a |- (
  PISFirstInvariant A B C D E F
) <->
(
  (
    -u 1 <_ D
    /\
    D < C
  )
  /\
  (
    ( PISPrefixClosed B D )
    /\
    (
      ( PISCrossOrder B D ( D + 2 ) ( C + 2 ) )
      /\
      (
        ( PISSuffixOrder B ( D + 2 ) ( C + 2 ) )
        /\
        (
          ( PISStrictLower B E ( D + 2 ) ( C + 2 ) )
          /\
          (
            PISPerm
              A
              (
                PISSet
                  ( PISSet B ( D + 1 ) F )
                  ( D + 2 )
                  E
              )
          )
        )
      )
    )
  )
) $.

$( A=original, B=current, C=i, D=j, E=smaller. $)
pis-second-invariant-definition $a |- (
  PISSecondInvariant A B C D E
) <->
(
  (
    -u 1 <_ D
    /\
    D < C
  )
  /\
  (
    ( PISPrefixClosed B D )
    /\
    (
      ( PISCrossOrder B D ( D + 1 ) ( C + 2 ) )
      /\
      (
        ( PISSuffixOrder B ( D + 1 ) ( C + 2 ) )
        /\
        (
          ( PISWeakLower B E ( D + 1 ) ( C + 2 ) )
          /\
          ( PISPerm A ( PISSet B ( D + 1 ) E ) )
        )
      )
    )
  )
) $.

$( A=original, B=outer anchor, C=final list, D=i. $)
pis-outer-next-definition $a |- (
  PISOuterNext A B C D
) <->
(
  (
    0 <_ ( ( # ` B ) - D )
    /\
    ( ( # ` C ) - ( D + 2 ) ) < ( ( # ` B ) - D )
  )
  /\
  (
    (
      0 <_ ( D + 2 )
      /\
      ( D + 2 ) <_ ( # ` C )
    )
    /\
    (
      ( PISSortedBefore C ( D + 2 ) )
      /\
      ( PISPerm A C )
    )
  )
) $.

$( A=original, B=current, C=i, D=j, E=smaller. $)
pis-second-shift-definition $a |- (
  PISSecondShift A B C D E
) <->
(
  (
    0 <_ D
    /\
    D < ( # ` B )
  )
  /\
  (
    (
      0 <_ ( D + 1 )
      /\
      ( D + 1 ) < ( # ` B )
    )
    /\
    (
      (
        ( # ` ( PISSet B ( D + 1 ) ( PISAt B D ) ) )
        =
        ( # ` B )
      )
      ->
      (
        ( PISSetLaw B ( D + 1 ) ( PISAt B D ) )
        ->
        (
          (
            0 <_ D
            /\
            ( D - 1 ) < D
          )
          /\
          (
            PISSecondInvariant
              A
              ( PISSet B ( D + 1 ) ( PISAt B D ) )
              C
              ( D - 1 )
              E
          )
        )
      )
    )
  )
) $.

$( A=original, B=outer anchor, C=current, D=i, E=j, F=smaller. $)
pis-second-finish-definition $a |- (
  PISSecondFinish A B C D E F
) <->
(
  (
    0 <_ ( E + 1 )
    /\
    ( E + 1 ) < ( # ` C )
  )
  /\
  (
    (
      ( # ` ( PISSet C ( E + 1 ) F ) )
      =
      ( # ` C )
    )
    ->
    (
      ( PISSetLaw C ( E + 1 ) F )
      ->
      (
        PISOuterNext
          A
          B
          ( PISSet C ( E + 1 ) F )
          D
      )
    )
  )
) $.

$( A=original, B=outer anchor, C=current, D=i, E=j, F=smaller. $)
pis-second-step-definition $a |- (
  PISSecondStep A B C D E F
) <->
(
  (
    0 <_ E
    ->
    (
      0 <_ E
      /\
      E < ( # ` C )
    )
  )
  /\
  (
    (
      (
        0 <_ E
        /\
        F < ( PISAt C E )
      )
      /\
      ( PISSecondShift A C D E F )
    )
    \/
    (
      -.
      (
        0 <_ E
        /\
        F < ( PISAt C E )
      )
      /\
      ( PISSecondFinish A B C D E F )
    )
  )
) $.

$( A=original, B=outer anchor, C=initial, D=i, E=j, F=smaller. $)
${
  $d j x A B C D E F $.

  pis-second-phase-definition $a |- (
    PISSecondPhase A B C D E F
  ) <->
  (
    ( PISSecondInvariant A C D E F )
    /\
    A. j e. ZZ
      A. x e. Word ZZ
        (
          ( ( # ` x ) = ( # ` C ) )
          ->
          (
            ( PISSecondInvariant A x D j F )
            ->
            ( PISSecondStep A B x D j F )
          )
        )
  ) $.
$}

$( A=original, B=current, C=i, D=j, E=larger, F=smaller. $)
pis-first-shift-definition $a |- (
  PISFirstShift A B C D E F
) <->
(
  (
    0 <_ D
    /\
    D < ( # ` B )
  )
  /\
  (
    (
      0 <_ ( D + 2 )
      /\
      ( D + 2 ) < ( # ` B )
    )
    /\
    (
      (
        ( # ` ( PISSet B ( D + 2 ) ( PISAt B D ) ) )
        =
        ( # ` B )
      )
      ->
      (
        ( PISSetLaw B ( D + 2 ) ( PISAt B D ) )
        ->
        (
          (
            0 <_ D
            /\
            ( D - 1 ) < D
          )
          /\
          (
            PISFirstInvariant
              A
              ( PISSet B ( D + 2 ) ( PISAt B D ) )
              C
              ( D - 1 )
              E
              F
          )
        )
      )
    )
  )
) $.

$( A=original, B=outer anchor, C=current, D=i, E=j,
   F=larger, G=smaller. $)
pis-first-finish-definition $a |- (
  PISFirstFinish A B C D E F G
) <->
(
  (
    0 <_ ( E + 2 )
    /\
    ( E + 2 ) < ( # ` C )
  )
  /\
  (
    (
      ( # ` ( PISSet C ( E + 2 ) F ) )
      =
      ( # ` C )
    )
    ->
    (
      ( PISSetLaw C ( E + 2 ) F )
      ->
      (
        PISSecondPhase
          A
          B
          ( PISSet C ( E + 2 ) F )
          D
          E
          G
      )
    )
  )
) $.

$( A=original, B=outer anchor, C=current, D=i, E=j,
   F=larger, G=smaller. $)
pis-first-step-definition $a |- (
  PISFirstStep A B C D E F G
) <->
(
  (
    0 <_ E
    ->
    (
      0 <_ E
      /\
      E < ( # ` C )
    )
  )
  /\
  (
    (
      (
        0 <_ E
        /\
        F < ( PISAt C E )
      )
      /\
      ( PISFirstShift A C D E F G )
    )
    \/
    (
      -.
      (
        0 <_ E
        /\
        F < ( PISAt C E )
      )
      /\
      ( PISFirstFinish A B C D E F G )
    )
  )
) $.

$( A=original, B=initial, C=i, D=larger, E=smaller. $)
${
  $d j x A B C D E $.

  pis-first-phase-definition $a |- (
    PISFirstPhase A B C D E
  ) <->
  (
    ( PISFirstInvariant A B C ( C - 1 ) D E )
    /\
    A. j e. ZZ
      A. x e. Word ZZ
        (
          ( ( # ` x ) = ( # ` B ) )
          ->
          (
            ( PISFirstInvariant A x C j D E )
            ->
            ( PISFirstStep A B x C j D E )
          )
        )
  ) $.
$}

$( A=original, B=current, C=i. $)
pis-pair-case-definition $a |- (
  PISPairCase A B C
) <->
(
  (
    0 <_ C
    /\
    C < ( # ` B )
  )
  /\
  (
    (
      0 <_ ( C + 1 )
      /\
      ( C + 1 ) < ( # ` B )
    )
    /\
    (
      (
        ( PISAt B C ) < ( PISAt B ( C + 1 ) )
        /\
        (
          PISFirstPhase
            A B C ( PISAt B ( C + 1 ) ) ( PISAt B C )
        )
      )
      \/
      (
        -. ( PISAt B C ) < ( PISAt B ( C + 1 ) )
        /\
        (
          PISFirstPhase
            A B C ( PISAt B C ) ( PISAt B ( C + 1 ) )
        )
      )
    )
  )
) $.

$( A=original, B=current, C=i, D=j, E=value. $)
pis-single-invariant-definition $a |- (
  PISSingleInvariant A B C D E
) <->
(
  (
    -u 1 <_ D
    /\
    D < C
  )
  /\
  (
    ( PISPrefixClosed B D )
    /\
    (
      ( PISCrossOrder B D ( D + 1 ) ( # ` B ) )
      /\
      (
        ( PISSuffixOrder B ( D + 1 ) ( # ` B ) )
        /\
        (
          ( PISStrictLower B E ( D + 1 ) ( # ` B ) )
          /\
          ( PISPerm A ( PISSet B ( D + 1 ) E ) )
        )
      )
    )
  )
) $.

$( A=original, B=current, C=i, D=j, E=value. $)
pis-single-shift-definition $a |- (
  PISSingleShift A B C D E
) <->
(
  (
    0 <_ D
    /\
    D < ( # ` B )
  )
  /\
  (
    (
      0 <_ ( D + 1 )
      /\
      ( D + 1 ) < ( # ` B )
    )
    /\
    (
      (
        ( # ` ( PISSet B ( D + 1 ) ( PISAt B D ) ) )
        =
        ( # ` B )
      )
      ->
      (
        ( PISSetLaw B ( D + 1 ) ( PISAt B D ) )
        ->
        (
          (
            0 <_ D
            /\
            ( D - 1 ) < D
          )
          /\
          (
            PISSingleInvariant
              A
              ( PISSet B ( D + 1 ) ( PISAt B D ) )
              C
              ( D - 1 )
              E
          )
        )
      )
    )
  )
) $.

$( A=original, B=current, C=j, D=value. $)
pis-single-finish-definition $a |- (
  PISSingleFinish A B C D
) <->
(
  (
    0 <_ ( C + 1 )
    /\
    ( C + 1 ) < ( # ` B )
  )
  /\
  (
    (
      ( # ` ( PISSet B ( C + 1 ) D ) )
      =
      ( # ` B )
    )
    ->
    (
      ( PISSetLaw B ( C + 1 ) D )
      ->
      (
        ( PISSortedBefore
            ( PISSet B ( C + 1 ) D )
            ( # ` ( PISSet B ( C + 1 ) D ) ) )
        /\
        ( PISPerm A ( PISSet B ( C + 1 ) D ) )
      )
    )
  )
) $.

$( A=original, B=current, C=i, D=j, E=value. $)
pis-single-step-definition $a |- (
  PISSingleStep A B C D E
) <->
(
  (
    0 <_ D
    ->
    (
      0 <_ D
      /\
      D < ( # ` B )
    )
  )
  /\
  (
    (
      (
        0 <_ D
        /\
        E < ( PISAt B D )
      )
      /\
      ( PISSingleShift A B C D E )
    )
    \/
    (
      -.
      (
        0 <_ D
        /\
        E < ( PISAt B D )
      )
      /\
      ( PISSingleFinish A B D E )
    )
  )
) $.

$( A=original, B=initial, C=i. $)
${
  $d j x A B C $.

  pis-single-phase-definition $a |- (
    PISSinglePhase A B C
  ) <->
  (
    (
      PISSingleInvariant
        A B C ( C - 1 ) ( PISAt B C )
    )
    /\
    A. j e. ZZ
      A. x e. Word ZZ
        (
          ( ( # ` x ) = ( # ` B ) )
          ->
          (
            (
              PISSingleInvariant
                A x C j ( PISAt B C )
            )
            ->
            (
              PISSingleStep
                A x C j ( PISAt B C )
            )
          )
        )
  ) $.
$}

$( A=original, B=current, C=i. $)
pis-single-case-definition $a |- (
  PISSingleCase A B C
) <->
(
  (
    0 <_ C
    /\
    C < ( # ` B )
  )
  /\
  ( PISSinglePhase A B C )
) $.

$( A=original, B=current, C=i. $)
pis-outer-step-definition $a |- (
  PISOuterStep A B C
) <->
(
  (
    (
      C < ( ( # ` B ) - 1 )
      /\
      ( PISPairCase A B C )
    )
    \/
    (
      -. C < ( ( # ` B ) - 1 )
      /\
      (
        (
          C = ( ( # ` B ) - 1 )
          /\
          ( PISSingleCase A B C )
        )
        \/
        (
          -. ( C = ( ( # ` B ) - 1 ) )
          /\
          (
            ( PISSortedBefore B ( # ` B ) )
            /\
            ( PISPerm A B )
          )
        )
      )
    )
  )
) $.

${
  $d i x A $.

  pis-all-outer-definition $a |- (
    PISAllOuter A
  ) <->
  A. i e. ZZ
    A. x e. Word ZZ
      (
        ( ( # ` x ) = ( # ` A ) )
        ->
        (
          (
            (
              0 <_ i
              /\
              i <_ ( # ` x )
            )
            /\
            (
              ( PISSortedBefore x i )
              /\
              ( PISPerm A x )
            )
          )
          ->
          ( PISOuterStep A x i )
        )
      ) $.
$}

pis-main-definition $a |- (
  PISMain A
) <->
(
  (
    0 <_ 0
    /\
    0 <_ ( # ` A )
  )
  /\
  (
    ( PISSortedBefore A 0 )
    /\
    (
      ( PISPerm A A )
      /\
      ( PISAllOuter A )
    )
  )
) $.

${
  ntp4vc-pair-insertion-sort-challenge1-vc $a |-
    A. a e. Word ZZ
      ( PISMain a ) $.
$}
