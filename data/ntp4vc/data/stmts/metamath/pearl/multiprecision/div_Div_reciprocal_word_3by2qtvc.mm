$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_reciprocal_word_3by2qtvc: the verification
  condition for constructing a reciprocal approximation for a normalized
  two-limb unsigned divisor, including carry and borrow corrections and the
  final three-by-two reciprocal identity. This file contains no proof.

  Source 64-bit words are represented exactly by the integer interval
  [0, 2^64 - 1], in bijection with their unsigned values. The normalization
  hypothesis makes the divisors in reciprocal and reciprocal_3by2 positive,
  so Metamath's floor quotient and modulo agree with Why3's Euclidean
  operations. Boolean values are represented by 2 = {0, 1}, with 1 for true
  and 0 for false. Proposition-valued conditionals are expanded into their
  two implication branches. The predicates below are definitional
  abbreviations for the source's nested quantifiers and implications.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord64 NTP4VCUInt64InBounds NTP4VCReciprocal
  NTP4VCReciprocal3 NTP4VCBoolGuard NTP4VCFlagOutcome
  NTP4VCFinalConditional NTP4VCProductStage
  NTP4VCHighCarryBranch NTP4VCLowCarryBranch NTP4VCMainBranch
  NTP4VCAfterO3 NTP4VCAfterO2 NTP4VCAfterO1
$.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-reciprocal-syntax
  $a wff ( NTP4VCReciprocal A B ) $.
ntp4vc-reciprocal3-syntax
  $a wff ( NTP4VCReciprocal3 A B C ) $.
ntp4vc-bool-guard-syntax
  $a wff ( NTP4VCBoolGuard A B C D E ) $.
ntp4vc-flag-outcome-syntax
  $a wff ( NTP4VCFlagOutcome A B C D ) $.
ntp4vc-final-conditional-syntax
  $a wff ( NTP4VCFinalConditional A B C D E F ) $.
ntp4vc-product-stage-syntax
  $a wff ( NTP4VCProductStage A B C D ) $.
ntp4vc-high-carry-branch-syntax
  $a wff ( NTP4VCHighCarryBranch A B C D ) $.
ntp4vc-low-carry-branch-syntax
  $a wff ( NTP4VCLowCarryBranch A B C D ) $.
ntp4vc-main-branch-syntax
  $a wff ( NTP4VCMainBranch A B C D ) $.
ntp4vc-after-o3-syntax
  $a wff ( NTP4VCAfterO3 A B C D ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-uint64-in-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. NTP4VCWord64
) $.

ntp4vc-reciprocal-definition $a |- (
  NTP4VCReciprocal A B
) <-> (
  A =
  (
    ( |_ `
      (
        (
          (
            ( 2 ^ ; 6 4 )
            x.
            ( 2 ^ ; 6 4 )
          )
          -
          1
        )
        /
        B
      )
    )
    -
    ( 2 ^ ; 6 4 )
  )
) $.

ntp4vc-reciprocal3-definition $a |- (
  NTP4VCReciprocal3 A B C
) <-> (
  A =
  (
    ( |_ `
      (
        (
          (
            (
              ( 2 ^ ; 6 4 )
              x.
              ( 2 ^ ; 6 4 )
            )
            x.
            ( 2 ^ ; 6 4 )
          )
          -
          1
        )
        /
        (
          C
          +
          ( ( 2 ^ ; 6 4 ) x. B )
        )
      )
    )
    -
    ( 2 ^ ; 6 4 )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-bool-guard-definition $a |- (
    NTP4VCBoolGuard A B C D E
  ) <-> (
    (
      A < B
      ->
      E = 1
    )
    /\
    (
      -. A < B
      ->
      E. q e. { 0 , 1 }
        (
          (
            (
              B = A
              ->
              q = 1
            )
            /\
            (
              q = 1
              ->
              B = A
            )
          )
          /\
          E =
          if (
            q = 1 ,
            if ( C <_ D , 1 , 0 ) ,
            0
          )
        )
    )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.
  $d q r $.

  ntp4vc-flag-outcome-definition $a |- (
    NTP4VCFlagOutcome A B C D
  ) <-> (
    (
      A = 1
      ->
      (
        ( NTP4VCUInt64InBounds ( B - 1 ) )
        /\
        A. q e. NTP4VCWord64
          (
            q = ( B - 1 )
            ->
            (
              ( NTP4VCUInt64InBounds ( q - 1 ) )
              /\
              A. r e. NTP4VCWord64
                (
                  r = ( q - 1 )
                  ->
                  ( NTP4VCReciprocal3 r C D )
                )
            )
          )
      )
    )
    /\
    (
      -. A = 1
      ->
      (
        ( NTP4VCUInt64InBounds ( B - 1 ) )
        /\
        A. q e. NTP4VCWord64
          (
            q = ( B - 1 )
            ->
            ( NTP4VCReciprocal3 q C D )
          )
      )
    )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.
  $d q D $.  $d q E $.  $d q F $.

  ntp4vc-final-conditional-definition $a |- (
    NTP4VCFinalConditional A B C D E F
  ) <-> (
    (
      A < B
      ->
      A. q e. { 0 , 1 }
        (
          ( NTP4VCBoolGuard C A D E q )
          ->
          ( NTP4VCFlagOutcome q F C D )
        )
    )
    /\
    (
      -. A < B
      ->
      ( NTP4VCReciprocal3 F C D )
    )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.
  $d s A $.  $d s B $.  $d s C $.  $d s D $.
  $d q r $.  $d q s $.  $d r s $.

  ntp4vc-product-stage-definition $a |- (
    NTP4VCProductStage A B C D
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            q + ( ( 2 ^ ; 6 4 ) x. r )
          )
          =
          ( B x. D )
          ->
          A. s e. NTP4VCWord64
            (
              s =
              (
                ( A + r )
                mod
                ( 2 ^ ; 6 4 )
              )
              ->
              ( NTP4VCFinalConditional s r C D q B )
            )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.
  $d s A $.  $d s B $.  $d s C $.  $d s D $.
  $d t A $.  $d t B $.  $d t C $.  $d t D $.
  $d q r $.  $d q s $.  $d q t $.
  $d r s $.  $d r t $.  $d s t $.

  ntp4vc-high-carry-branch-definition $a |- (
    NTP4VCHighCarryBranch A B C D
  ) <-> (
    ( NTP4VCUInt64InBounds ( A - 1 ) )
    /\
    A. q e. NTP4VCWord64
      (
        q = ( A - 1 )
        ->
        (
          ( NTP4VCUInt64InBounds ( B - C ) )
          /\
          A. r e. NTP4VCWord64
            (
              r = ( B - C )
              ->
              (
                ( NTP4VCUInt64InBounds ( q - 1 ) )
                /\
                A. s e. NTP4VCWord64
                  (
                    s = ( q - 1 )
                    ->
                    A. t e. NTP4VCWord64
                      (
                        t =
                        (
                          ( r - C )
                          mod
                          ( 2 ^ ; 6 4 )
                        )
                        ->
                        ( NTP4VCProductStage t s C D )
                      )
                  )
              )
            )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.
  $d q r $.

  ntp4vc-low-carry-branch-definition $a |- (
    NTP4VCLowCarryBranch A B C D
  ) <-> (
    ( NTP4VCUInt64InBounds ( A - 1 ) )
    /\
    A. q e. NTP4VCWord64
      (
        q = ( A - 1 )
        ->
        A. r e. NTP4VCWord64
          (
            r =
            (
              ( B - C )
              mod
              ( 2 ^ ; 6 4 )
            )
            ->
            ( NTP4VCProductStage r q C D )
          )
      )
  ) $.
$}

ntp4vc-main-branch-definition $a |- (
  NTP4VCMainBranch A B C D
) <-> (
  (
    B < D
    ->
    (
      (
        C <_ B
        ->
        ( NTP4VCHighCarryBranch A B C D )
      )
      /\
      (
        -. C <_ B
        ->
        ( NTP4VCLowCarryBranch A B C D )
      )
    )
  )
  /\
  (
    -. B < D
    ->
    ( NTP4VCProductStage B A C D )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.

  ntp4vc-after-o3-definition $a |- (
    NTP4VCAfterO3 A B C D
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( B + D )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        ( NTP4VCMainBranch A q C D )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( B x. A )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        ( NTP4VCAfterO3 A q B C )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B
  ) <-> (
    A. q e. NTP4VCWord64
      (
        ( NTP4VCReciprocal q A )
        ->
        ( NTP4VCAfterO2 q A B )
      )
  ) $.
$}

${
  $( Source parameters: A=dh and B=dl. $)

  ntp4vc-dh-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-dl-word64 $e |- B e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- (
    ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) )
    <_
    A
  ) $.

  ntp4vc-pearl-multiprecision-div-reciprocal-word-3by2-vc $a |- (
    (
      ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) )
      <_
      A
    )
    /\
    ( NTP4VCAfterO1 A B )
  ) $.
$}
