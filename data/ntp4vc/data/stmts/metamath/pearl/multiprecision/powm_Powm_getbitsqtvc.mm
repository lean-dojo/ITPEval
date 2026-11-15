$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitsqtvc: the verification condition for
  extracting a nonempty bit window from a valid multiprecision unsigned
  integer, including the one-limb and two-limb cases, exact word bounds,
  shifted pointer views, masking arithmetic, and the value-prefix
  reconstruction equations. This file contains no proof.

  Unsigned 32- and 64-bit words are represented by their complete bounded
  integer carriers, and signed 32-bit values use exact two's-complement
  interpretation. A pointer retains the source finite limb sequence, integer
  offset and bounds, Boolean writability field, and arbitrary nonempty zone.
  NTP4VCValue and NTP4VCValueB definitionally render the source little-endian
  radix-2^64 value functions. NTP4VCTDiv and NTP4VCTMod render truncating
  integer quotient and remainder; the other displayed quotients and moduli
  are the source Euclidean operations with positive divisors. The final
  quotient-and-mask equation is guarded by nbits <= bi; the complementary
  low-bit branch is characterized by its value-prefix equation.

  The Lean 4 and Isabelle ground truths agree on computing the limb quotient
  before the within-limb remainder. The Rocq export interchanges those two
  binders locally; this statement follows the canonical
  quotient-before-remainder control flow and the established NTP4VC encoding.
  The helper predicates below are explicit definitional abbreviations for the
  nested quantifiers, implications, and conditional branches, so expansion is
  a bidirectional logical equivalence.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCUInt64InBounds NTP4VCPtr NTP4VCData NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCPeltsEq NTP4VCValid NTP4VCValue NTP4VCIPow
  NTP4VCTDiv NTP4VCTMod NTP4VCValueB NTP4VCShiftCopy
  NTP4VCResultPost NTP4VCReducedResult NTP4VCSmallBranch
  NTP4VCOneLimbBranch NTP4VCTwoLimbBranch NTP4VCLargeBranch
  NTP4VCGetBitsVC
$.

$v
  result o1 o2 difference quotient remainder o4 ntp4vcpone o5 shifted
  remaining o7 o8 partial o9 ntp4vcptwo o10 o11 o12
$.

ntp4vc-result-variable $f setvar result $.
ntp4vc-o1-variable $f setvar o1 $.
ntp4vc-o2-variable $f setvar o2 $.
ntp4vc-difference-variable $f setvar difference $.
ntp4vc-quotient-variable $f setvar quotient $.
ntp4vc-remainder-variable $f setvar remainder $.
ntp4vc-o4-variable $f setvar o4 $.
ntp4vc-p1-variable $f setvar ntp4vcpone $.
ntp4vc-o5-variable $f setvar o5 $.
ntp4vc-shifted-variable $f setvar shifted $.
ntp4vc-remaining-variable $f setvar remaining $.
ntp4vc-o7-variable $f setvar o7 $.
ntp4vc-o8-variable $f setvar o8 $.
ntp4vc-partial-variable $f setvar partial $.
ntp4vc-o9-variable $f setvar o9 $.
ntp4vc-p2-variable $f setvar ntp4vcptwo $.
ntp4vc-o10-variable $f setvar o10 $.
ntp4vc-o11-variable $f setvar o11 $.
ntp4vc-o12-variable $f setvar o12 $.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syntax
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
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
ntp4vc-ipow-syntax $a class ( NTP4VCIPow A B ) $.
ntp4vc-tdiv-syntax $a class ( NTP4VCTDiv A B ) $.
ntp4vc-tmod-syntax $a class ( NTP4VCTMod A B ) $.
ntp4vc-valueb-syntax $a class ( NTP4VCValueB A B ) $.
ntp4vc-shift-copy-syntax
  $a wff ( NTP4VCShiftCopy A B C ) $.
ntp4vc-result-post-syntax
  $a wff ( NTP4VCResultPost A B C D E ) $.
ntp4vc-reduced-result-syntax
  $a wff ( NTP4VCReducedResult A B C D E F ) $.
ntp4vc-small-branch-syntax
  $a wff ( NTP4VCSmallBranch A B C D ) $.
ntp4vc-one-limb-branch-syntax
  $a wff ( NTP4VCOneLimbBranch A B C D E ) $.
ntp4vc-two-limb-branch-syntax
  $a wff ( NTP4VCTwoLimbBranch A B C D E F G H ) $.
ntp4vc-large-branch-syntax
  $a wff ( NTP4VCLargeBranch A B C D E ) $.
ntp4vc-getbits-vc-syntax
  $a wff ( NTP4VCGetBitsVC A B C D E ) $.

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

ntp4vc-uint64-in-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. ZZ
  /\
  (
    0 <_ A
    /\
    A < ( 2 ^ ; 6 4 )
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

ntp4vc-ipow-definition $a |- (
  NTP4VCIPow A B
) = ( A ^ ( NTP4VCToNat B ) ) $.

ntp4vc-tdiv-definition $a |- (
  NTP4VCTDiv A B
) = if (
  A < 0 ,
  ( |^ ` ( A / B ) ) ,
  ( |_ ` ( A / B ) )
) $.

ntp4vc-tmod-definition $a |- (
  NTP4VCTMod A B
) = ( A - ( B x. ( NTP4VCTDiv A B ) ) ) $.

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

ntp4vc-result-post-definition $a |- (
  NTP4VCResultPost A B C D E
) <-> (
  (
    (
      ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 C )
      ->
      (
        NTP4VCValueB A ( NTP4VCSigned32 C )
      )
      =
      (
        (
          NTP4VCValueB A
            (
              ( NTP4VCSigned32 C )
              -
              ( NTP4VCSigned32 D )
            )
        )
        +
        (
          (
            NTP4VCIPow 2
              (
                ( NTP4VCSigned32 C )
                -
                ( NTP4VCSigned32 D )
              )
          )
          x. E
        )
      )
    )
    /\
    (
      (
        ( NTP4VCSigned32 C ) < ( NTP4VCSigned32 D )
        ->
        ( NTP4VCValueB A ( NTP4VCSigned32 C ) ) = E
      )
      /\
      (
        (
          0 <_ E
          /\
          E < ( NTP4VCIPow 2 ( NTP4VCSigned32 D ) )
        )
        /\
        (
          ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 C )
          ->
          E
          =
          (
            (
              |_ `
              (
                ( NTP4VCValue A ( NTP4VCSigned32 B ) )
                /
                (
                  NTP4VCIPow 2
                    (
                      ( NTP4VCSigned32 C )
                      -
                      ( NTP4VCSigned32 D )
                    )
                )
              )
            )
            mod
            (
              NTP4VCIPow 2
                (
                  NTP4VCSigned32 D
                )
            )
          )
        )
      )
    )
  )
) $.

${
  $d result A B C D E F $.

  ntp4vc-reduced-result-definition $a |- (
    NTP4VCReducedResult A B C D E F
  ) <-> (
    ( -. F = 0 )
    /\
    (
      ( NTP4VCUInt64InBounds ( NTP4VCTMod E F ) )
      /\
      A. result e. NTP4VCWord64
        (
          result = ( NTP4VCTMod E F )
          ->
          ( NTP4VCResultPost A B C D result )
        )
    )
  ) $.
$}

${
  $d o1 o2 A B C D $.

  ntp4vc-small-branch-definition $a |- (
    NTP4VCSmallBranch A B C D
  ) <-> (
    0 <_ ( NTP4VCSigned32 C )
    /\
    A. o1 e. NTP4VCWord64
      (
        o1 = ( NTP4VCSigned32 C )
        ->
        (
          (
            (
              0 <_ o1
              /\
              o1 < ; 6 4
            )
            /\
            (
              ( ( NTP4VCIPow 2 o1 ) x. 1 )
              <_
              ( ( 2 ^ ; 6 4 ) - 1 )
            )
          )
          /\
          A. o2 e. NTP4VCWord64
            (
              o2 = ( ( NTP4VCIPow 2 o1 ) x. 1 )
              ->
              (
                (
                  ( NTP4VCMin A ) <_ ( NTP4VCOffset A )
                  /\
                  ( NTP4VCOffset A ) < ( NTP4VCMax A )
                )
                /\
                (
                  NTP4VCReducedResult A B C D
                    ( NTP4VCPelts A ( NTP4VCOffset A ) ) o2
                )
              )
            )
        )
      )
  ) $.
$}

${
  $d o7 o8 A B C D E $.

  ntp4vc-one-limb-branch-definition $a |- (
    NTP4VCOneLimbBranch A B C D E
  ) <-> (
    0 <_ ( NTP4VCSigned32 D )
    /\
    A. o7 e. NTP4VCWord64
      (
        o7 = ( NTP4VCSigned32 D )
        ->
        (
          (
            (
              0 <_ o7
              /\
              o7 < ; 6 4
            )
            /\
            (
              ( ( NTP4VCIPow 2 o7 ) x. 1 )
              <_
              ( ( 2 ^ ; 6 4 ) - 1 )
            )
          )
          /\
          A. o8 e. NTP4VCWord64
            (
              o8 = ( ( NTP4VCIPow 2 o7 ) x. 1 )
              ->
              ( NTP4VCReducedResult A B C D E o8 )
            )
        )
      )
  ) $.
$}

${
  $d o7 o8 partial o9 ntp4vcptwo o10 o11 o12
     A B C D E F G H $.

  ntp4vc-two-limb-branch-definition $a |- (
    NTP4VCTwoLimbBranch A B C D E F G H
  ) <-> (
    ( NTP4VCInt32InBounds ( ( NTP4VCSigned32 E ) + 1 ) )
    /\
    A. o7 e. NTP4VCWord32
      (
        ( NTP4VCSigned32 o7 ) = ( ( NTP4VCSigned32 E ) + 1 )
        ->
        (
          (
            ( NTP4VCMin A )
            <_
            ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 o7 ) )
            /\
            ( ( NTP4VCOffset A ) + ( NTP4VCSigned32 o7 ) )
            <
            ( NTP4VCMax A )
          )
          /\
          (
            0 <_ ( NTP4VCSigned32 G )
            /\
            A. o8 e. NTP4VCWord64
              (
                o8 = ( NTP4VCSigned32 G )
                ->
                (
                  (
                    0 <_ o8
                    /\
                    o8 < ; 6 4
                  )
                  /\
                  A. partial e. NTP4VCWord64
                    (
                      (
                        partial
                        =
                        (
                          (
                            (
                              NTP4VCPelts A
                                (
                                  ( NTP4VCOffset A )
                                  +
                                  ( NTP4VCSigned32 o7 )
                                )
                            )
                            x.
                            ( NTP4VCIPow 2 o8 )
                          )
                          mod
                          ( 2 ^ ; 6 4 )
                        )
                        /\
                        partial
                        <_
                        (
                          ( 2 ^ ; 6 4 )
                          -
                          ( NTP4VCIPow 2 o8 )
                        )
                      )
                      ->
                      (
                        (
                          NTP4VCInt32InBounds
                            ( ( NTP4VCSigned32 E ) + 2 )
                        )
                        /\
                        A. o9 e. NTP4VCWord32
                          (
                            ( NTP4VCSigned32 o9 )
                            =
                            ( ( NTP4VCSigned32 E ) + 2 )
                            ->
                            (
                              (
                                ( NTP4VCMin A )
                                <_
                                (
                                  ( NTP4VCOffset A )
                                  +
                                  ( NTP4VCSigned32 o9 )
                                )
                                /\
                                (
                                  ( NTP4VCOffset A )
                                  +
                                  ( NTP4VCSigned32 o9 )
                                )
                                <_
                                ( NTP4VCMax A )
                              )
                              /\
                              A. ntp4vcptwo e. ( NTP4VCPtr H )
                                (
                                  (
                                    NTP4VCShiftCopy ntp4vcptwo A
                                      ( NTP4VCSigned32 o9 )
                                  )
                                  ->
                                  (
                                    ( -. ( 2 ^ ; 6 4 ) = 0 )
                                    /\
                                    (
                                      (
                                        NTP4VCUInt64InBounds
                                          ( F + partial )
                                      )
                                      /\
                                      A. o10 e. NTP4VCWord64
                                        (
                                          o10 = ( F + partial )
                                          ->
                                          (
                                            0 <_ ( NTP4VCSigned32 D )
                                            /\
                                            A. o11 e. NTP4VCWord64
                                              (
                                                o11
                                                =
                                                ( NTP4VCSigned32 D )
                                                ->
                                                (
                                                  (
                                                    (
                                                      0 <_ o11
                                                      /\
                                                      o11 < ; 6 4
                                                    )
                                                    /\
                                                    (
                                                      (
                                                        ( NTP4VCIPow 2 o11 )
                                                        x. 1
                                                      )
                                                      <_
                                                      (
                                                        ( 2 ^ ; 6 4 )
                                                        - 1
                                                      )
                                                    )
                                                  )
                                                  /\
                                                  A. o12 e. NTP4VCWord64
                                                    (
                                                      o12
                                                      =
                                                      (
                                                        (
                                                          NTP4VCIPow 2 o11
                                                        )
                                                        x. 1
                                                      )
                                                      ->
                                                      (
                                                        NTP4VCReducedResult
                                                          A B C D o10 o12
                                                      )
                                                    )
                                                )
                                              )
                                          )
                                        )
                                    )
                                  )
                                )
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
$}

${
  $d difference quotient remainder o4 ntp4vcpone o5 shifted remaining
     A B C D E $.

  ntp4vc-large-branch-definition $a |- (
    NTP4VCLargeBranch A B C D E
  ) <-> (
    (
      NTP4VCInt32InBounds
        (
          ( NTP4VCSigned32 C )
          -
          ( NTP4VCSigned32 D )
        )
    )
    /\
    A. difference e. NTP4VCWord32
      (
        ( NTP4VCSigned32 difference )
        =
        (
          ( NTP4VCSigned32 C )
          -
          ( NTP4VCSigned32 D )
        )
        ->
        (
          (
            ( -. ; 6 4 = 0 )
            /\
            (
              NTP4VCInt32InBounds
                (
                  NTP4VCTDiv
                    ( NTP4VCSigned32 difference )
                    ; 6 4
                )
            )
          )
          /\
          A. quotient e. NTP4VCWord32
            (
              ( NTP4VCSigned32 quotient )
              =
              (
                NTP4VCTDiv
                  ( NTP4VCSigned32 difference )
                  ; 6 4
              )
              ->
              (
                (
                  ( -. ; 6 4 = 0 )
                  /\
                  (
                    NTP4VCInt32InBounds
                      (
                        NTP4VCTMod
                          ( NTP4VCSigned32 difference )
                          ; 6 4
                      )
                  )
                )
                /\
                A. remainder e. NTP4VCWord32
                  (
                    ( NTP4VCSigned32 remainder )
                    =
                    (
                      NTP4VCTMod
                        ( NTP4VCSigned32 difference )
                        ; 6 4
                    )
                    ->
                    (
                      (
                        ( NTP4VCMin A )
                        <_
                        (
                          ( NTP4VCOffset A )
                          +
                          ( NTP4VCSigned32 quotient )
                        )
                        /\
                        (
                          ( NTP4VCOffset A )
                          +
                          ( NTP4VCSigned32 quotient )
                        )
                        <
                        ( NTP4VCMax A )
                      )
                      /\
                      (
                        (
                          NTP4VCInt32InBounds
                            ( ( NTP4VCSigned32 quotient ) + 1 )
                        )
                        /\
                        A. o4 e. NTP4VCWord32
                          (
                            ( NTP4VCSigned32 o4 )
                            =
                            ( ( NTP4VCSigned32 quotient ) + 1 )
                            ->
                            (
                              (
                                ( NTP4VCMin A )
                                <_
                                (
                                  ( NTP4VCOffset A )
                                  +
                                  ( NTP4VCSigned32 o4 )
                                )
                                /\
                                (
                                  ( NTP4VCOffset A )
                                  +
                                  ( NTP4VCSigned32 o4 )
                                )
                                <_
                                ( NTP4VCMax A )
                              )
                              /\
                              A. ntp4vcpone e. ( NTP4VCPtr E )
                                (
                                  (
                                    NTP4VCShiftCopy ntp4vcpone A
                                      ( NTP4VCSigned32 o4 )
                                  )
                                  ->
                                  (
                                    0 <_ ( NTP4VCSigned32 remainder )
                                    /\
                                    A. o5 e. NTP4VCWord64
                                      (
                                        o5
                                        =
                                        ( NTP4VCSigned32 remainder )
                                        ->
                                        (
                                          (
                                            0 <_ o5
                                            /\
                                            o5 < ; 6 4
                                          )
                                          /\
                                          A. shifted e. NTP4VCWord64
                                            (
                                              shifted
                                              =
                                              (
                                                |_ `
                                                (
                                                  (
                                                    NTP4VCPelts A
                                                      (
                                                        (
                                                          NTP4VCOffset A
                                                        )
                                                        +
                                                        (
                                                          NTP4VCSigned32
                                                            quotient
                                                        )
                                                      )
                                                  )
                                                  /
                                                  (
                                                    NTP4VCIPow 2 o5
                                                  )
                                                )
                                              )
                                              ->
                                              (
                                                (
                                                  -.
                                                  (
                                                    NTP4VCIPow 2
                                                      (
                                                        NTP4VCSigned32
                                                          remainder
                                                      )
                                                  )
                                                  =
                                                  0
                                                )
                                                /\
                                                (
                                                  (
                                                    NTP4VCInt32InBounds
                                                      (
                                                        ; 6 4
                                                        -
                                                        (
                                                          NTP4VCSigned32
                                                            remainder
                                                        )
                                                      )
                                                  )
                                                  /\
                                                  A. remaining
                                                    e. NTP4VCWord32
                                                    (
                                                      (
                                                        NTP4VCSigned32
                                                          remaining
                                                      )
                                                      =
                                                      (
                                                        ; 6 4
                                                        -
                                                        (
                                                          NTP4VCSigned32
                                                            remainder
                                                        )
                                                      )
                                                      ->
                                                      (
                                                        (
                                                          (
                                                            NTP4VCSigned32
                                                              remaining
                                                          )
                                                          <
                                                          (
                                                            NTP4VCSigned32
                                                              D
                                                          )
                                                          /\
                                                          (
                                                            NTP4VCTwoLimbBranch
                                                              A B C D
                                                              quotient
                                                              shifted
                                                              remaining E
                                                          )
                                                        )
                                                        \/
                                                        (
                                                          -.
                                                          (
                                                            (
                                                              NTP4VCSigned32
                                                                remaining
                                                            )
                                                            <
                                                            (
                                                              NTP4VCSigned32
                                                                D
                                                            )
                                                          )
                                                          /\
                                                          (
                                                            NTP4VCOneLimbBranch
                                                              A B C D shifted
                                                          )
                                                        )
                                                      )
                                                    )
                                                )
                                              )
                                            )
                                        )
                                      )
                                  )
                                )
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
$}

ntp4vc-getbits-vc-definition $a |- (
  NTP4VCGetBitsVC A B C D E
) <-> (
  (
    ( NTP4VCSigned32 C ) < ( NTP4VCSigned32 D )
    /\
    ( NTP4VCSmallBranch A B C D )
  )
  \/
  (
    -. ( ( NTP4VCSigned32 C ) < ( NTP4VCSigned32 D ) )
    /\
    ( NTP4VCLargeBranch A B C D E )
  )
) $.

${
  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-p-pointer $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-pn-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-bi-word32 $e |- C e. NTP4VCWord32 $.
  ntp4vc-nbits-word32 $e |- D e. NTP4VCWord32 $.
  ntp4vc-fact0 $e |- 1 <_ ( NTP4VCSigned32 D ) $.
  ntp4vc-fact1 $e |- ( NTP4VCSigned32 D ) < ; 6 4 $.
  ntp4vc-fact2 $e |- 0 <_ ( NTP4VCSigned32 C ) $.
  ntp4vc-fact3 $e |- 1 <_ ( NTP4VCSigned32 B ) $.
  ntp4vc-fact4 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact5 $e |- (
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

  ntp4vc-pearl-multiprecision-powm-getbits-vc $a |- (
    NTP4VCGetBitsVC A B C D Z
  ) $.
$}
