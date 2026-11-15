$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div2by1_invqtvc: the verification condition
  for reciprocal-based division of a two-limb unsigned integer by a
  normalized 64-bit divisor, including carry reconstruction, quotient
  correction, and remainder bounds. This file contains no proof.

  Source 64-bit words are represented exactly by the integer interval
  [0, 2^64 - 1], in bijection with their unsigned values. Since every
  divisor used by division or modulo is positive under the source
  hypotheses, Metamath's floor quotient and modulo agree with Why3's
  Euclidean operations. The predicates below are definitional abbreviations
  for the original nested universal quantifiers, implications, and
  proposition-valued conditionals.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord64 NTP4VCUInt64InBounds NTP4VCReciprocal
  NTP4VCResult NTP4VCAfterO6 NTP4VCAfterO5
  NTP4VCFirstAfterO4 NTP4VCFirstAfterO3
  NTP4VCSecondAfterO4 NTP4VCSecondAfterO3
  NTP4VCCorrectionBranches NTP4VCAfterO2 NTP4VCAfterP
  NTP4VCAfterO1 NTP4VCHighAdd NTP4VCLowAdd
$.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-reciprocal-syntax
  $a wff ( NTP4VCReciprocal A B ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D E ) $.
ntp4vc-after-o6-syntax
  $a wff ( NTP4VCAfterO6 A B C D E ) $.
ntp4vc-after-o5-syntax
  $a wff ( NTP4VCAfterO5 A B C D E ) $.
ntp4vc-first-after-o4-syntax
  $a wff ( NTP4VCFirstAfterO4 A B C D E ) $.
ntp4vc-first-after-o3-syntax
  $a wff ( NTP4VCFirstAfterO3 A B C D E ) $.
ntp4vc-second-after-o4-syntax
  $a wff ( NTP4VCSecondAfterO4 A B C D E ) $.
ntp4vc-second-after-o3-syntax
  $a wff ( NTP4VCSecondAfterO3 A B C D E ) $.
ntp4vc-correction-branches-syntax
  $a wff ( NTP4VCCorrectionBranches A B C D E F ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C D E F ) $.
ntp4vc-after-p-syntax
  $a wff ( NTP4VCAfterP A B C D E ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E ) $.
ntp4vc-high-add-syntax
  $a wff ( NTP4VCHighAdd A B C D E F ) $.
ntp4vc-low-add-syntax
  $a wff ( NTP4VCLowAdd A B C D E ) $.

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

ntp4vc-result-definition $a |- (
  NTP4VCResult A B C D E
) <-> (
  (
    ( ( A x. C ) + B )
    =
    ( E + ( ( 2 ^ ; 6 4 ) x. D ) )
  )
  /\
  (
    0 <_ B
    /\
    B < C
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-after-o6-definition $a |- (
    NTP4VCAfterO6 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( E - A )
        ->
        ( NTP4VCResult D q A B C )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-after-o5-definition $a |- (
    NTP4VCAfterO5 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( D + 1 )
        ->
        (
          ( NTP4VCUInt64InBounds ( E - A ) )
          /\
          ( NTP4VCAfterO6 A B C q E )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-first-after-o4-definition $a |- (
    NTP4VCFirstAfterO4 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( ( E + A ) mod ( 2 ^ ; 6 4 ) )
        ->
        (
          (
            A <_ q
            ->
            (
              ( NTP4VCUInt64InBounds ( D + 1 ) )
              /\
              ( NTP4VCAfterO5 A B C D q )
            )
          )
          /\
          (
            -. A <_ q
            ->
            ( NTP4VCResult D q A B C )
          )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-first-after-o3-definition $a |- (
    NTP4VCFirstAfterO3 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( ( D - 1 ) mod ( 2 ^ ; 6 4 ) )
        ->
        ( NTP4VCFirstAfterO4 A B C q E )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-second-after-o4-definition $a |- (
    NTP4VCSecondAfterO4 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( E - A )
        ->
        ( NTP4VCResult D q A B C )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-second-after-o3-definition $a |- (
    NTP4VCSecondAfterO3 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( D + 1 )
        ->
        (
          ( NTP4VCUInt64InBounds ( E - A ) )
          /\
          ( NTP4VCSecondAfterO4 A B C q E )
        )
      )
  ) $.
$}

ntp4vc-correction-branches-definition $a |- (
  NTP4VCCorrectionBranches A B C D E F
) <-> (
  (
    D < F
    ->
    ( NTP4VCFirstAfterO3 A B C E F )
  )
  /\
  (
    -. D < F
    ->
    (
      (
        A <_ F
        ->
        (
          ( NTP4VCUInt64InBounds ( E + 1 ) )
          /\
          ( NTP4VCSecondAfterO3 A B C E F )
        )
      )
      /\
      (
        -. A <_ F
        ->
        ( NTP4VCResult E F A B C )
      )
    )
  )
) $.

${
  $d q A $.  $d q B $.  $d q C $.
  $d q D $.  $d q E $.  $d q F $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C D E F
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( ( C - F ) mod ( 2 ^ ; 6 4 ) )
        ->
        ( NTP4VCCorrectionBranches A B C D E q )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-after-p-definition $a |- (
    NTP4VCAfterP A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( ( E x. A ) mod ( 2 ^ ; 6 4 ) )
        ->
        ( NTP4VCAfterO2 A B C D E q )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = ( ( E + 1 ) mod ( 2 ^ ; 6 4 ) )
        ->
        ( NTP4VCAfterP A B C D q )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.
  $d q D $.  $d q E $.  $d q F $.
  $d r A $.  $d r B $.  $d r C $.
  $d r D $.  $d r E $.  $d r F $.
  $d q r $.

  ntp4vc-high-add-definition $a |- (
    NTP4VCHighAdd A B C D E F
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              ( q + ( ( 2 ^ ; 6 4 ) x. r ) )
              =
              ( ( B + C ) + F )
            )
            /\
            (
              0 <_ r
              /\
              r <_ 1
            )
          )
          ->
          ( NTP4VCAfterO1 A B D E q )
        )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r E $.
  $d q r $.

  ntp4vc-low-add-definition $a |- (
    NTP4VCLowAdd A B C D E
  ) <-> (
    A. q e. NTP4VCWord64
      A. r e. NTP4VCWord64
        (
          (
            (
              ( q + ( ( 2 ^ ; 6 4 ) x. r ) )
              =
              ( ( C + E ) + 0 )
            )
            /\
            (
              0 <_ r
              /\
              r <_ 1
            )
          )
          ->
          (
            (
              0 <_ r
              /\
              r <_ 1
            )
            /\
            ( NTP4VCHighAdd A B D E q r )
          )
        )
  ) $.
$}

${
  $( Source parameters: A=d, B=uh, C=v, D=l, E=h, and F=ul. $)

  ntp4vc-d-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-uh-word64 $e |- B e. NTP4VCWord64 $.
  ntp4vc-v-word64 $e |- C e. NTP4VCWord64 $.
  ntp4vc-l-word64 $e |- D e. NTP4VCWord64 $.
  ntp4vc-h-word64 $e |- E e. NTP4VCWord64 $.
  ntp4vc-ul-word64 $e |- F e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- (
    ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) )
    <_
    A
  ) $.

  ntp4vc-fact1 $e |- B < A $.

  ntp4vc-fact2 $e |- ( NTP4VCReciprocal C A ) $.

  ntp4vc-fact3 $e |- (
    D + ( ( 2 ^ ; 6 4 ) x. E )
  ) = (
    C x. B
  ) $.

  ntp4vc-pearl-multiprecision-div-div2by1-inv-vc $a |- (
    0 <_ 0
    /\
    (
      0 <_ 1
      /\
      ( NTP4VCLowAdd A B D E F )
    )
  ) $.
$}
