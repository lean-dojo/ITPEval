$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div3by2_invqtvc: the verification condition
  for reciprocal-based division of a three-limb unsigned integer by a
  normalized two-limb divisor, including modular carry and borrow
  reconstruction, quotient correction, and remainder bounds. This file
  contains no proof.

  Source 64-bit words are represented exactly by the integer interval
  [0, 2^64 - 1], in bijection with their unsigned values. The divisor in
  reciprocal_3by2 is positive under the normalization hypothesis, so
  Metamath's floor quotient agrees with Why3's Euclidean division. Boolean
  values are represented by 2 = {0, 1}, with 1 for true and 0 for false.
  Proposition-valued conditionals are expanded into their two implication
  branches. The predicates below are definitional abbreviations for the
  original nested universal and existential quantifiers and implications.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord64 NTP4VCBit NTP4VCReciprocal3 NTP4VCResult
  NTP4VCBoolGuard NTP4VCCorrectionHigh NTP4VCCorrectionLow
  NTP4VCFlagBranch NTP4VCGuardedOutcome NTP4VCAddHigh
  NTP4VCAddLow NTP4VCDecrementBranch NTP4VCCorrectionBranches
  NTP4VCSecondHighBorrow NTP4VCSecondLowBorrow
  NTP4VCFirstHighBorrow NTP4VCFirstLowBorrow NTP4VCProduct
  NTP4VCAfterO2 NTP4VCAfterP NTP4VCAfterO1
  NTP4VCHighAdd NTP4VCLowAdd
$.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-bit-syntax $a wff ( NTP4VCBit A ) $.
ntp4vc-reciprocal3-syntax
  $a wff ( NTP4VCReciprocal3 A B C ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D E F G H ) $.
ntp4vc-bool-guard-syntax
  $a wff ( NTP4VCBoolGuard A B C D E ) $.
ntp4vc-correction-high-syntax
  $a wff ( NTP4VCCorrectionHigh A B C D E F G H I ) $.
ntp4vc-correction-low-syntax
  $a wff ( NTP4VCCorrectionLow A B C D E F G H ) $.
ntp4vc-flag-branch-syntax
  $a wff ( NTP4VCFlagBranch A B C D E F G H I ) $.
ntp4vc-guarded-outcome-syntax
  $a wff ( NTP4VCGuardedOutcome A B C D E F G H ) $.
ntp4vc-add-high-syntax
  $a wff ( NTP4VCAddHigh A B C D E F G H I ) $.
ntp4vc-add-low-syntax
  $a wff ( NTP4VCAddLow A B C D E F G H ) $.
ntp4vc-decrement-branch-syntax
  $a wff ( NTP4VCDecrementBranch A B C D E F G H ) $.
ntp4vc-correction-branches-syntax
  $a wff ( NTP4VCCorrectionBranches A B C D E F G H I ) $.
ntp4vc-second-high-borrow-syntax
  $a wff ( NTP4VCSecondHighBorrow A B C D E F G H I J ) $.
ntp4vc-second-low-borrow-syntax
  $a wff ( NTP4VCSecondLowBorrow A B C D E F G H I ) $.
ntp4vc-first-high-borrow-syntax
  $a wff ( NTP4VCFirstHighBorrow A B C D E F G H I J K ) $.
ntp4vc-first-low-borrow-syntax
  $a wff ( NTP4VCFirstLowBorrow A B C D E F G H I J ) $.
ntp4vc-product-syntax
  $a wff ( NTP4VCProduct A B C D E F G H I ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C D E F G H I ) $.
ntp4vc-after-p-syntax
  $a wff ( NTP4VCAfterP A B C D E F G H ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E F G ) $.
ntp4vc-high-add-syntax
  $a wff ( NTP4VCHighAdd A B C D E F G H ) $.
ntp4vc-low-add-syntax
  $a wff ( NTP4VCLowAdd A B C D E F G ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-bit-definition $a |- (
  NTP4VCBit A
) <-> (
  0 <_ A
  /\
  A <_ 1
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

ntp4vc-result-definition $a |- (
  NTP4VCResult A B C D E F G H
) <-> (
  (
    (
      (
        (
          ( F x. A )
          +
          ( ( ( 2 ^ ; 6 4 ) x. F ) x. B )
        )
        +
        G
      )
      +
      ( ( 2 ^ ; 6 4 ) x. H )
    )
    =
    (
      (
        C
        +
        ( ( 2 ^ ; 6 4 ) x. D )
      )
      +
      (
        (
          ( 2 ^ ; 6 4 )
          x.
          ( 2 ^ ; 6 4 )
        )
        x.
        E
      )
    )
  )
  /\
  (
    0 <_ ( G + ( ( 2 ^ ; 6 4 ) x. H ) )
    /\
    (
      ( G + ( ( 2 ^ ; 6 4 ) x. H ) )
      <
      ( A + ( ( 2 ^ ; 6 4 ) x. B ) )
    )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-bool-guard-definition $a |- (
    NTP4VCBoolGuard A B C D E
  ) <-> (
    (
      A < C
      ->
      E = 1
    )
    /\
    (
      -. A < C
      ->
      E. q e. { 0 , 1 }
        (
          (
            (
              C = A
              ->
              q = 1
            )
            /\
            (
              q = 1
              ->
              C = A
            )
          )
          /\
          E =
          if (
            q = 1 ,
            if ( B <_ D , 1 , 0 ) ,
            0
          )
        )
    )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.
  $d s A $.  $d s B $.  $d s C $.  $d s D $.  $d s E $.
  $d s F $.  $d s G $.  $d s H $.  $d s I $.
  $d q r $.
  $d q s $.
  $d r s $.

  ntp4vc-correction-high-definition $a |- (
    NTP4VCCorrectionHigh A B C D E F G H I
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( H - B ) - I
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          A. s e. NTP4VCWord64
            (
              s =
              (
                ( F + 1 )
                mod
                ( 2 ^ ; 6 4 )
              )
              ->
              ( NTP4VCResult A B C D E s G q )
            )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.
  $d q r $.

  ntp4vc-correction-low-definition $a |- (
    NTP4VCCorrectionLow A B C D E F G H
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( G - A ) - 0
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            ( NTP4VCBit r )
            /\
            ( NTP4VCCorrectionHigh A B C D E F q H r )
          )
        )
  ) $.
$}

ntp4vc-flag-branch-definition $a |- (
  NTP4VCFlagBranch A B C D E F G H I
) <-> (
  (
    I = 1
    ->
    (
      (
        0 <_ 0
        /\
        0 <_ 1
      )
      /\
      ( NTP4VCCorrectionLow A B C D E F G H )
    )
  )
  /\
  (
    -. I = 1
    ->
    ( NTP4VCResult A B C D E F G H )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.

  ntp4vc-guarded-outcome-definition $a |- (
    NTP4VCGuardedOutcome A B C D E F G H
  ) <-> (
    A. q e. { 0 , 1 }
      (
        ( NTP4VCBoolGuard B A H G q )
        ->
        ( NTP4VCFlagBranch A B C D E F G H q )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.
  $d q r $.

  ntp4vc-add-high-definition $a |- (
    NTP4VCAddHigh A B C D E F G H I
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q + ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( H + B ) + I
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          ( NTP4VCGuardedOutcome A B C D E F G q )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.
  $d q r $.

  ntp4vc-add-low-definition $a |- (
    NTP4VCAddLow A B C D E F G H
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q + ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( G + A ) + 0
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            ( NTP4VCBit r )
            /\
            ( NTP4VCAddHigh A B C D E F q H r )
          )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.

  ntp4vc-decrement-branch-definition $a |- (
    NTP4VCDecrementBranch A B C D E F G H
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( F - 1 )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        (
          (
            0 <_ 0
            /\
            0 <_ 1
          )
          /\
          ( NTP4VCAddLow A B C D E q G H )
        )
      )
  ) $.
$}

ntp4vc-correction-branches-definition $a |- (
  NTP4VCCorrectionBranches A B C D E F G H I
) <-> (
  (
    F <_ I
    ->
    ( NTP4VCDecrementBranch A B C D E G H I )
  )
  /\
  (
    -. F <_ I
    ->
    ( NTP4VCGuardedOutcome A B C D E G H I )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.  $d q J $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.  $d r J $.
  $d q r $.

  ntp4vc-second-high-borrow-definition $a |- (
    NTP4VCSecondHighBorrow A B C D E F G H I J
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( I - B ) - J
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          ( NTP4VCCorrectionBranches A B C D E F G H q )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.
  $d q r $.

  ntp4vc-second-low-borrow-definition $a |- (
    NTP4VCSecondLowBorrow A B C D E F G H I
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( H - A ) - 0
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            ( NTP4VCBit r )
            /\
            ( NTP4VCSecondHighBorrow A B C D E F G q I r )
          )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.  $d q J $.
  $d q K $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.  $d r J $.
  $d r K $.
  $d q r $.

  ntp4vc-first-high-borrow-definition $a |- (
    NTP4VCFirstHighBorrow A B C D E F G H I J K
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( H - I ) - K
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            (
              0 <_ 0
              /\
              0 <_ 1
            )
            /\
            ( NTP4VCSecondLowBorrow A B C D E F G J q )
          )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.  $d q J $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.  $d r J $.
  $d q r $.

  ntp4vc-first-low-borrow-definition $a |- (
    NTP4VCFirstLowBorrow A B C D E F G H I J
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q - ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( C - I ) - 0
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            ( NTP4VCBit r )
            /\
            ( NTP4VCFirstHighBorrow A B C D E F G H J q r )
          )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.  $d r I $.
  $d q r $.

  ntp4vc-product-definition $a |- (
    NTP4VCProduct A B C D E F G H I
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            q + ( ( 2 ^ ; 6 4 ) x. r )
          )
          =
          ( I x. A )
          ->
          (
            (
              0 <_ 0
              /\
              0 <_ 1
            )
            /\
            ( NTP4VCFirstLowBorrow A B C D E F G H q r )
          )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C D E F G H I
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( D - I )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        (
          -. ( 2 ^ ; 6 4 ) = 0
          /\
          ( NTP4VCProduct A B C D E F G q H )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.

  ntp4vc-after-p-definition $a |- (
    NTP4VCAfterP A B C D E F G H
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( B x. H )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        ( NTP4VCAfterO2 A B C D E F G H q )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E F G
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( G + 1 )
          mod
          ( 2 ^ ; 6 4 )
        )
        ->
        ( NTP4VCAfterP A B C D E F q G )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.  $d r H $.
  $d q r $.

  ntp4vc-high-add-definition $a |- (
    NTP4VCHighAdd A B C D E F G H
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q + ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( E + F ) + H
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          ( NTP4VCAfterO1 A B C D E G q )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d r F $.  $d r G $.
  $d q r $.

  ntp4vc-low-add-definition $a |- (
    NTP4VCLowAdd A B C D E F G
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              q + ( ( 2 ^ ; 6 4 ) x. r )
            )
            =
            (
              ( D + F ) + 0
            )
            /\
            ( NTP4VCBit r )
          )
          ->
          (
            ( NTP4VCBit r )
            /\
            ( NTP4VCHighAdd A B C D E G q r )
          )
        )
  ) $.
$}

${
  $(
    Source parameters:
    A=dh, B=v, C=dl, D=um, E=uh, F=l, G=h, and H=ul.
  $)

  ntp4vc-dh-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-v-word64 $e |- B e. NTP4VCWord64 $.
  ntp4vc-dl-word64 $e |- C e. NTP4VCWord64 $.
  ntp4vc-um-word64 $e |- D e. NTP4VCWord64 $.
  ntp4vc-uh-word64 $e |- E e. NTP4VCWord64 $.
  ntp4vc-l-word64 $e |- F e. NTP4VCWord64 $.
  ntp4vc-h-word64 $e |- G e. NTP4VCWord64 $.
  ntp4vc-ul-word64 $e |- H e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- (
    ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) )
    <_
    A
  ) $.

  ntp4vc-fact1 $e |- ( NTP4VCReciprocal3 B A C ) $.

  ntp4vc-fact2 $e |- (
    D + ( ( 2 ^ ; 6 4 ) x. E )
  ) < (
    C + ( ( 2 ^ ; 6 4 ) x. A )
  ) $.

  ntp4vc-fact3 $e |- (
    F + ( ( 2 ^ ; 6 4 ) x. G )
  ) = (
    B x. E
  ) $.

  ntp4vc-pearl-multiprecision-div-div3by2-inv-vc $a |- (
    0 <_ 0
    /\
    (
      0 <_ 1
      /\
      ( NTP4VCLowAdd C A H D E F G )
    )
  ) $.
$}
