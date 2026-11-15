$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitqtvc: the verification condition for
  extracting one bit from a valid multiprecision unsigned integer, including
  exact word bounds, pointer indexing, shifted-limb arithmetic, the returned
  bit, and the value-prefix reconstruction identity. This file contains no
  proof.

  Unsigned 32- and 64-bit words are represented by their complete bounded
  integer carriers, and signed 32-bit values use exact two's-complement
  interpretation. A pointer retains the source finite limb sequence, integer
  offset and bounds, Boolean writability field, and arbitrary nonempty zone.
  NTP4VCValue and NTP4VCValueB are definitional renderings of the source
  little-endian radix-2^64 value functions. All translated divisions and
  remainders have positive divisors and nonnegative dividends under their
  enclosing hypotheses, so floor quotient and mod agree with Why3's
  Euclidean operations. The stage predicates below only factor the original
  nested universal quantifiers and implications.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCPtr NTP4VCData NTP4VCOffset NTP4VCMin NTP4VCMax
  NTP4VCWritable NTP4VCZone NTP4VCToNat NTP4VCPelts
  NTP4VCPeltsEq NTP4VCValid NTP4VCValue NTP4VCValueB
  NTP4VCShiftCopy NTP4VCFinalResult NTP4VCAfterRes
  NTP4VCAfterLps NTP4VCAfterPtr NTP4VCAfterO4 NTP4VCAfterMi
  NTP4VCAfterO3 NTP4VCAfterO2 NTP4VCAfterI NTP4VCAfterO1
$.

$v result res lps o1 o2 o3 o4 mi $.

ntp4vc-result-variable $f setvar result $.
ntp4vc-res-variable $f setvar res $.
ntp4vc-lps-variable $f setvar lps $.
ntp4vc-o1-variable $f setvar o1 $.
ntp4vc-o2-variable $f setvar o2 $.
ntp4vc-o3-variable $f setvar o3 $.
ntp4vc-o4-variable $f setvar o4 $.
ntp4vc-mi-variable $f setvar mi $.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-ptr-syntax $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syntax $a class ( NTP4VCData A ) $.
ntp4vc-offset-syntax $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A ) $.
ntp4vc-max-syntax $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syntax $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syntax $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syntax $a class ( NTP4VCPelts A B ) $.
ntp4vc-pelts-eq-syntax $a wff ( NTP4VCPeltsEq A B ) $.
ntp4vc-valid-syntax $a wff ( NTP4VCValid A B ) $.
ntp4vc-value-syntax $a class ( NTP4VCValue A B ) $.
ntp4vc-valueb-syntax $a class ( NTP4VCValueB A B ) $.
ntp4vc-shift-copy-syntax
  $a wff ( NTP4VCShiftCopy A B C ) $.
ntp4vc-final-result-syntax
  $a wff ( NTP4VCFinalResult A B C D ) $.
ntp4vc-after-res-syntax
  $a wff ( NTP4VCAfterRes A B C D ) $.
ntp4vc-after-lps-syntax
  $a wff ( NTP4VCAfterLps A B C D ) $.
ntp4vc-after-ptr-syntax
  $a wff ( NTP4VCAfterPtr A B C D E ) $.
ntp4vc-after-o4-syntax
  $a wff ( NTP4VCAfterO4 A B C D E F G ) $.
ntp4vc-after-mi-syntax
  $a wff ( NTP4VCAfterMi A B C D E F ) $.
ntp4vc-after-o3-syntax
  $a wff ( NTP4VCAfterO3 A B C D E F ) $.
ntp4vc-after-o2-syntax
  $a wff ( NTP4VCAfterO2 A B C D E F ) $.
ntp4vc-after-i-syntax
  $a wff ( NTP4VCAfterI A B C D E ) $.
ntp4vc-after-o1-syntax
  $a wff ( NTP4VCAfterO1 A B C D E ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- (
  NTP4VCSigned32 A
) = if (
  A < ( 2 ^ ; 3 1 ) ,
  A ,
  ( A - ( 2 ^ ; 3 2 ) )
) $.

ntp4vc-int32-in-bounds-definition $a |- (
  NTP4VCInt32InBounds A
) <-> (
  A e. ZZ
  /\
  (
    ( -u ( 2 ^ ; 3 1 ) ) <_ A
    /\
    A < ( 2 ^ ; 3 1 )
  )
) $.

ntp4vc-ptr-definition $a |- (
  NTP4VCPtr A
) = (
  ( Word NTP4VCWord64 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) )
) $.

ntp4vc-data-definition $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-offset-definition $a |- (
  NTP4VCOffset A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-definition $a |- (
  NTP4VCMin A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-definition $a |- (
  NTP4VCMax A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-writable-definition $a |- (
  NTP4VCWritable A
) = (
  1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
) $.

ntp4vc-zone-definition $a |- (
  NTP4VCZone A
) = (
  2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) )
) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-pelts-definition $a |- (
  NTP4VCPelts A B
) = if (
  ( NTP4VCToNat B ) < ( # ` ( NTP4VCData A ) ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d j A B $.

  ntp4vc-pelts-eq-definition $a |- (
    NTP4VCPeltsEq A B
  ) <-> (
    A. j e. ZZ
      ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
  ) $.
$}

ntp4vc-valid-definition $a |- (
  NTP4VCValid A B
) <-> (
  ( NTP4VCInt32InBounds B )
  /\
  (
    0 <_ B
    /\
    (
      (
        0 <_ ( NTP4VCMin A )
        /\
        ( NTP4VCMin A ) <_ ( NTP4VCOffset A )
      )
      /\
      (
        (
          ( NTP4VCOffset A ) + B
        ) <_ ( NTP4VCMax A )
        /\
        ( NTP4VCMax A ) <_ ( # ` ( NTP4VCData A ) )
      )
    )
  )
) $.

${
  $d k A B $.

  ntp4vc-value-definition $a |- (
    NTP4VCValue A B
  ) = (
    sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
      (
        ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) )
        x.
        ( ( 2 ^ ; 6 4 ) ^ k )
      )
  ) $.
$}

ntp4vc-valueb-definition $a |- (
  NTP4VCValueB A B
) = if (
  B < 0 ,
  0 ,
  (
    (
      NTP4VCValue A
        ( |_ ` ( B / ; 6 4 ) )
    )
    +
    (
      (
        ( 2 ^ ; 6 4 )
        ^
        ( |_ ` ( B / ; 6 4 ) )
      )
      x.
      (
        (
          NTP4VCPelts A
            (
              ( NTP4VCOffset A )
              +
              ( |_ ` ( B / ; 6 4 ) )
            )
        )
        mod
        (
          2
          ^
          (
            B
            -
            (
              ; 6 4
              x.
              ( |_ ` ( B / ; 6 4 ) )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-shift-copy-definition $a |- (
  NTP4VCShiftCopy A B C
) <-> (
  ( NTP4VCOffset A ) = ( ( NTP4VCOffset B ) + C )
  /\
  (
    ( # ` ( NTP4VCData A ) ) = ( # ` ( NTP4VCData B ) )
    /\
    (
      ( NTP4VCPeltsEq A B )
      /\
      (
        ( NTP4VCData A ) = ( NTP4VCData B )
        /\
        (
          ( NTP4VCMin A ) = ( NTP4VCMin B )
          /\
          (
            ( NTP4VCMax A ) = ( NTP4VCMax B )
            /\
            (
              ( NTP4VCZone A ) = ( NTP4VCZone B )
              /\
              ( NTP4VCWritable A ) = ( NTP4VCWritable B )
            )
          )
        )
      )
    )
  )
) $.

ntp4vc-final-result-definition $a |- (
  NTP4VCFinalResult A B C D
) <-> (
  (
    0 <_ D
    /\
    D <_ 1
  )
  /\
  (
    D
    =
    (
      (
        |_ `
        (
          ( NTP4VCValue A ( NTP4VCSigned32 B ) )
          /
          (
            2
            ^
            (
              ( NTP4VCSigned32 C ) - 1
            )
          )
        )
      )
      mod 2
    )
    /\
    (
      NTP4VCValueB A ( NTP4VCSigned32 C )
    )
    =
    (
      (
        NTP4VCValueB A
          ( ( NTP4VCSigned32 C ) - 1 )
      )
      +
      (
        (
          2
          ^
          (
            ( NTP4VCSigned32 C ) - 1
          )
        )
        x.
        D
      )
    )
  )
) $.

${
  $d result A B C D $.

  ntp4vc-after-res-definition $a |- (
    NTP4VCAfterRes A B C D
  ) <-> (
    A. result e. NTP4VCWord64
      (
        result = ( D mod 2 )
        ->
        ( NTP4VCFinalResult A B C result )
      )
  ) $.
$}

${
  $d res A B C D $.

  ntp4vc-after-lps-definition $a |- (
    NTP4VCAfterLps A B C D
  ) <-> (
    A. res e. NTP4VCWord64
      (
        res = ( D mod 2 )
        ->
        (
          ( -. 2 = 0 )
          /\
          (
            (
              ( -. 2 = 0 )
              /\
              ( ( D mod 2 ) e. NTP4VCWord64 )
            )
            /\
            ( NTP4VCAfterRes A B C D )
          )
        )
      )
  ) $.
$}

${
  $d lps A B C D E $.

  ntp4vc-after-ptr-definition $a |- (
    NTP4VCAfterPtr A B C D E
  ) <-> (
    A. lps e. NTP4VCWord64
      (
        lps
        =
        (
          |_ `
          (
            (
              NTP4VCPelts A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 D )
                )
            )
            /
            ( 2 ^ E )
          )
        )
        ->
        (
          ( -. ( 2 ^ E ) = 0 )
          /\
          (
            (
              ( -. 2 = 0 )
              /\
              ( ( lps mod 2 ) e. NTP4VCWord64 )
            )
            /\
            ( NTP4VCAfterLps A B C lps )
          )
        )
      )
  ) $.
$}

${
  $d p A B C D E F G $.

  ntp4vc-after-o4-definition $a |- (
    NTP4VCAfterO4 A B C D E F G
  ) <-> (
    (
      ( NTP4VCMin A )
      <_
      (
        ( NTP4VCOffset A )
        +
        ( NTP4VCSigned32 F )
      )
      /\
      (
        ( NTP4VCOffset A )
        +
        ( NTP4VCSigned32 F )
      )
      <_
      ( NTP4VCMax A )
    )
    /\
    A. p e. ( NTP4VCPtr G )
      (
        ( NTP4VCShiftCopy p A ( NTP4VCSigned32 F ) )
        ->
        (
          (
            0 <_ E
            /\
            E < ; 6 4
          )
          /\
          ( NTP4VCAfterPtr A B C D E )
        )
      )
  ) $.
$}

${
  $d o4 A B C D E F $.

  ntp4vc-after-mi-definition $a |- (
    NTP4VCAfterMi A B C D E F
  ) <-> (
    (
      ( NTP4VCMin A )
      <_
      (
        ( NTP4VCOffset A )
        +
        ( NTP4VCSigned32 D )
      )
      /\
      (
        ( NTP4VCOffset A )
        +
        ( NTP4VCSigned32 D )
      )
      <
      ( NTP4VCMax A )
    )
    /\
    (
      (
        NTP4VCInt32InBounds
          ( ( NTP4VCSigned32 D ) + 1 )
      )
      /\
      A. o4 e. NTP4VCWord32
        (
          (
            NTP4VCSigned32 o4
          )
          =
          (
            ( NTP4VCSigned32 D ) + 1
          )
          ->
          ( NTP4VCAfterO4 A B C D E o4 F )
        )
    )
  ) $.
$}

${
  $d mi A B C D E F $.

  ntp4vc-after-o3-definition $a |- (
    NTP4VCAfterO3 A B C D E F
  ) <-> (
    (
      ( -. ; 6 4 = 0 )
      /\
      ( ( E mod ; 6 4 ) e. NTP4VCWord64 )
    )
    /\
    A. mi e. NTP4VCWord64
      (
        mi = ( E mod ; 6 4 )
        ->
        ( NTP4VCAfterMi A B C D mi F )
      )
  ) $.
$}

${
  $d o3 A B C D E F $.

  ntp4vc-after-o2-definition $a |- (
    NTP4VCAfterO2 A B C D E F
  ) <-> (
    0 <_ ( NTP4VCSigned32 E )
    /\
    A. o3 e. NTP4VCWord64
      (
        o3 = ( NTP4VCSigned32 E )
        ->
        ( NTP4VCAfterO3 A B C D o3 F )
      )
  ) $.
$}

${
  $d o2 A B C D E $.

  ntp4vc-after-i-definition $a |- (
    NTP4VCAfterI A B C D E
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 C ) - 1 )
    )
    /\
    A. o2 e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 o2
        )
        =
        (
          ( NTP4VCSigned32 C ) - 1
        )
        ->
        ( NTP4VCAfterO2 A B C D o2 E )
      )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-after-o1-definition $a |- (
    NTP4VCAfterO1 A B C D E
  ) <-> (
    (
      ( -. ; 6 4 = 0 )
      /\
      (
        NTP4VCInt32InBounds
          (
            |_ `
            (
              ( NTP4VCSigned32 D )
              /
              ; 6 4
            )
          )
      )
    )
    /\
    A. i e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 i
        )
        =
        (
          |_ `
          (
            ( NTP4VCSigned32 D )
            /
            ; 6 4
          )
        )
        ->
        ( NTP4VCAfterI A B C i E )
      )
  ) $.
$}

${
  $d o1 A B C Z $.

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-p-pointer $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-pn-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-bi-word32 $e |- C e. NTP4VCWord32 $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- 1 <_ ( NTP4VCSigned32 C ) $.
  ntp4vc-fact2 $e |- (
    |_ `
    (
      (
        ( NTP4VCSigned32 C )
        +
        ; 6 3
      )
      /
      ; 6 4
    )
  ) <_ ( NTP4VCSigned32 B ) $.

  ntp4vc-pearl-multiprecision-powm-getbit-vc $a |- (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 C ) - 1 )
    )
    /\
    A. o1 e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 o1
        )
        =
        (
          ( NTP4VCSigned32 C ) - 1
        )
        ->
        ( NTP4VCAfterO1 A B C o1 Z )
      )
  ) $.
$}
