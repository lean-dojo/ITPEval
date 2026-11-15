$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1qtvc: the verification
  condition for subtracting a 64-bit limb from a positive-length
  multiprecision value into a separate writable destination, including
  modular limb updates, borrow propagation, the subsequent copy loop,
  pointer-state continuations, loop invariants, and memory framing.
  This file contains no proof.

  The 32- and 64-bit words use their complete canonical integer carriers,
  with exact two's-complement signed interpretation for 32-bit indices.
  Pointer data retain the Why3 array's total integer-indexed 64-bit limb map
  and independent nonnegative length, together with offset, bounds,
  writability, and zone. The predicates below are definitional factorizations
  of the source validity, positional value, functional-update, frame,
  invariant, branch, and continuation formulas. Expanding them yields the
  original nested verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSameMeta
  NTP4VCUpdateLaw NTP4VCBounds NTP4VCOutsideFrame
  NTP4VCBoolResult NTP4VCBorrowInvariant NTP4VCCopyInvariant
  NTP4VCFinal NTP4VCCopyAfterWrite NTP4VCCopyStep
  NTP4VCCopyStates NTP4VCAfterZeroTest NTP4VCBorrowAfterWrite
  NTP4VCBorrowWrite NTP4VCBorrowResult NTP4VCBorrowStep
  NTP4VCBorrowStates NTP4VCInitialBorrow NTP4VCInitialCopy
  NTP4VCAfterFirstWrite NTP4VCFirstWrite NTP4VCFirstResult
  NTP4VCVC
$.

ntp4vc-word32-syn $a class NTP4VCWord32 $.
ntp4vc-word64-syn $a class NTP4VCWord64 $.
ntp4vc-signed32-syn $a class ( NTP4VCSigned32 A ) $.
ntp4vc-int32-in-bounds-syn
  $a wff ( NTP4VCInt32InBounds A ) $.
ntp4vc-radix-syn $a class NTP4VCRadix $.
ntp4vc-ptr-syn $a class ( NTP4VCPtr A ) $.
ntp4vc-data-syn $a class ( NTP4VCData A ) $.
ntp4vc-length-syn $a class ( NTP4VCLength A ) $.
ntp4vc-offset-syn $a class ( NTP4VCOffset A ) $.
ntp4vc-min-syn $a class ( NTP4VCMin A ) $.
ntp4vc-max-syn $a class ( NTP4VCMax A ) $.
ntp4vc-writable-syn $a class ( NTP4VCWritable A ) $.
ntp4vc-zone-syn $a class ( NTP4VCZone A ) $.
ntp4vc-to-nat-syn $a class ( NTP4VCToNat A ) $.
ntp4vc-pelts-syn $a class ( NTP4VCPelts A B ) $.
ntp4vc-valid-syn $a wff ( NTP4VCValid A B ) $.
ntp4vc-value-syn $a class ( NTP4VCValue A B ) $.
ntp4vc-same-meta-syn $a wff ( NTP4VCSameMeta A B ) $.
ntp4vc-update-law-syn
  $a wff ( NTP4VCUpdateLaw A B C D ) $.
ntp4vc-bounds-syn $a wff ( NTP4VCBounds A B ) $.
ntp4vc-outside-frame-syn
  $a wff ( NTP4VCOutsideFrame A B C ) $.
ntp4vc-bool-result-syn $a wff ( NTP4VCBoolResult A B ) $.
ntp4vc-borrow-invariant-syn
  $a wff ( NTP4VCBorrowInvariant A B C D E F G ) $.
ntp4vc-copy-invariant-syn
  $a wff ( NTP4VCCopyInvariant A B C D E F G ) $.
ntp4vc-final-syn $a wff ( NTP4VCFinal A B C D E F ) $.
ntp4vc-copy-after-write-syn
  $a wff ( NTP4VCCopyAfterWrite A B C D E F G ) $.
ntp4vc-copy-step-syn
  $a wff ( NTP4VCCopyStep A B C D E F G H ) $.
ntp4vc-copy-states-syn
  $a wff ( NTP4VCCopyStates A B C D E F G ) $.
ntp4vc-after-zero-test-syn
  $a wff ( NTP4VCAfterZeroTest A B C D E F G H I J ) $.
ntp4vc-borrow-after-write-syn
  $a wff ( NTP4VCBorrowAfterWrite A B C D E F G H I ) $.
ntp4vc-borrow-write-syn
  $a wff ( NTP4VCBorrowWrite A B C D E F G H I ) $.
ntp4vc-borrow-result-syn
  $a wff ( NTP4VCBorrowResult A B C D E F G H ) $.
ntp4vc-borrow-step-syn
  $a wff ( NTP4VCBorrowStep A B C D E F G H ) $.
ntp4vc-borrow-states-syn
  $a wff ( NTP4VCBorrowStates A B C D E F ) $.
ntp4vc-initial-borrow-syn
  $a wff ( NTP4VCInitialBorrow A B C D E F ) $.
ntp4vc-initial-copy-syn
  $a wff ( NTP4VCInitialCopy A B C D E F ) $.
ntp4vc-after-first-write-syn
  $a wff ( NTP4VCAfterFirstWrite A B C D E F G ) $.
ntp4vc-first-write-syn
  $a wff ( NTP4VCFirstWrite A B C D E F G ) $.
ntp4vc-first-result-syn
  $a wff ( NTP4VCFirstResult A B C D E F ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C D E ) $.

ntp4vc-word32-def $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-def $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-def $a |- (
  NTP4VCSigned32 A
) = if (
  A < ( 2 ^ ; 3 1 ) ,
  A ,
  ( A - ( 2 ^ ; 3 2 ) )
) $.

ntp4vc-int32-in-bounds-def $a |- (
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

ntp4vc-radix-def $a |- NTP4VCRadix = ( 2 ^ ; 6 4 ) $.

ntp4vc-ptr-def $a |- (
  NTP4VCPtr A
) = (
  ( ( NTP4VCWord64 ^m ZZ ) X. NN0 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( 2 X. A ) ) ) )
) $.

ntp4vc-data-def $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-length-def $a |- (
  NTP4VCLength A
) = ( 2nd ` ( NTP4VCData A ) ) $.

ntp4vc-offset-def $a |- (
  NTP4VCOffset A
) = ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-min-def $a |- (
  NTP4VCMin A
) = ( 1st ` ( 2nd ` ( 2nd ` A ) ) ) $.

ntp4vc-max-def $a |- (
  NTP4VCMax A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) $.

ntp4vc-writable-def $a |- (
  NTP4VCWritable A
) = ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-zone-def $a |- (
  NTP4VCZone A
) = ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` A ) ) ) ) ) $.

ntp4vc-to-nat-def $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-pelts-def $a |- (
  NTP4VCPelts A B
) = ( ( 1st ` ( NTP4VCData A ) ) ` B ) $.

ntp4vc-valid-def $a |- (
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
        ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCMax A )
        /\
        ( NTP4VCMax A ) <_ ( NTP4VCLength A )
      )
    )
  )
) $.

${
  $d k A B $.

  ntp4vc-value-def $a |- (
    NTP4VCValue A B
  ) = (
    sum_ k e. ( 0 ..^ ( NTP4VCToNat B ) )
      (
        ( NTP4VCPelts A ( ( NTP4VCOffset A ) + k ) )
        x.
        ( NTP4VCRadix ^ k )
      )
  ) $.
$}

ntp4vc-same-meta-def $a |- (
  NTP4VCSameMeta A B
) <-> (
  ( NTP4VCLength A ) = ( NTP4VCLength B )
  /\
  (
    ( NTP4VCOffset A ) = ( NTP4VCOffset B )
    /\
    (
      ( NTP4VCMin A ) = ( NTP4VCMin B )
      /\
      (
        ( NTP4VCMax A ) = ( NTP4VCMax B )
        /\
        (
          ( NTP4VCWritable A ) = ( NTP4VCWritable B )
          /\
          ( NTP4VCZone A ) = ( NTP4VCZone B )
        )
      )
    )
  )
) $.

${
  $d j A B C D $.

  ntp4vc-update-law-def $a |- (
    NTP4VCUpdateLaw A B C D
  ) <-> (
    A. j e. ZZ
      (
        ( NTP4VCPelts B j )
        =
        if (
          j = C ,
          D ,
          ( NTP4VCPelts A j )
        )
      )
  ) $.
$}

ntp4vc-bounds-def $a |- (
  NTP4VCBounds A B
) <-> (
  ( NTP4VCMin A ) <_ ( ( NTP4VCOffset A ) + B )
  /\
  ( ( NTP4VCOffset A ) + B ) < ( NTP4VCMax A )
) $.

${
  $d j A B C $.

  ntp4vc-outside-frame-def $a |- (
    NTP4VCOutsideFrame A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          j < ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + C ) <_ j
        )
        ->
        ( NTP4VCPelts A j ) = ( NTP4VCPelts B j )
      )
  ) $.
$}

ntp4vc-bool-result-def $a |- (
  NTP4VCBoolResult A B
) <-> (
  ( A = 0 -> B = 1 )
  /\
  ( B = 1 -> A = 0 )
) $.

ntp4vc-borrow-invariant-def $a |- (
  NTP4VCBorrowInvariant A B C D E F G
) <-> (
  (
    1 <_ ( NTP4VCSigned32 D )
    /\
    ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 F )
  )
  /\
  (
    (
      0 <_ E
      /\
      E <_ 1
    )
    /\
    (
      (
        D = F
        \/
        E = 1
      )
      /\
      (
        (
          (
            NTP4VCValue A ( NTP4VCSigned32 D )
          )
          -
          (
            (
              NTP4VCRadix
              ^
              ( NTP4VCToNat ( NTP4VCSigned32 D ) )
            )
            x.
            E
          )
        ) = (
          (
            NTP4VCValue B ( NTP4VCSigned32 D )
          )
          -
          G
        )
        /\
        (
          NTP4VCOutsideFrame
            A C ( NTP4VCSigned32 F )
        )
      )
    )
  )
) $.

ntp4vc-copy-invariant-def $a |- (
  NTP4VCCopyInvariant A B C D E F G
) <-> (
  (
    D = F
    \/
    E = 0
  )
  /\
  (
    (
      0 <_ ( NTP4VCSigned32 D )
      /\
      ( NTP4VCSigned32 D ) <_ ( NTP4VCSigned32 F )
    )
    /\
    (
      (
        (
          NTP4VCValue A ( NTP4VCSigned32 D )
        )
        -
        (
          (
            NTP4VCRadix
            ^
            ( NTP4VCToNat ( NTP4VCSigned32 D ) )
          )
          x.
          E
        )
      ) = (
        (
          NTP4VCValue B ( NTP4VCSigned32 D )
        )
        -
        G
      )
      /\
      (
        NTP4VCOutsideFrame
          A C ( NTP4VCSigned32 F )
      )
    )
  )
) $.

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D E F
) <-> (
  (
    (
      NTP4VCValue A ( NTP4VCSigned32 D )
    )
    -
    (
      (
        NTP4VCRadix
        ^
        ( NTP4VCToNat ( NTP4VCSigned32 D ) )
      )
      x.
      F
    )
  ) = (
    (
      NTP4VCValue B ( NTP4VCSigned32 D )
    )
    -
    E
  )
  /\
  (
    (
      NTP4VCOutsideFrame
        A C ( NTP4VCSigned32 D )
    )
    /\
    (
      0 <_ F
      /\
      F <_ 1
    )
  )
) $.

${
  $d i A B C D E F G $.

  ntp4vc-copy-after-write-def $a |- (
    NTP4VCCopyAfterWrite A B C D E F G
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) + 1 )
    )
    /\
    A. i e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 i
        ) = (
          ( NTP4VCSigned32 D ) + 1
        )
        ->
        (
          (
            0 <_ (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 D )
            )
            /\
            (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 i )
            ) < (
              ( NTP4VCSigned32 F )
              -
              ( NTP4VCSigned32 D )
            )
          )
          /\
          (
            NTP4VCCopyInvariant
              A B C i E F G
          )
        )
      )
  ) $.
$}

${
  $d p A B C D E F G H $.

  ntp4vc-copy-step-def $a |- (
    NTP4VCCopyStep A B C D E F G H
  ) <-> (
    (
      (
        ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F )
        /\
        (
          ( NTP4VCBounds B ( NTP4VCSigned32 D ) )
          /\
          (
            (
              ( NTP4VCBounds A ( NTP4VCSigned32 D ) )
              /\
              ( NTP4VCWritable A ) = 1
            )
            /\
            A. p e. ( NTP4VCPtr H )
              (
                ( NTP4VCSameMeta p A )
                ->
                (
                  (
                    (
                      NTP4VCUpdateLaw
                        A p
                        (
                          ( NTP4VCOffset p )
                          +
                          ( NTP4VCSigned32 D )
                        )
                        (
                          NTP4VCPelts B
                          (
                            ( NTP4VCOffset B )
                            +
                            ( NTP4VCSigned32 D )
                          )
                        )
                    )
                    /\
                    (
                      NTP4VCPelts p
                      (
                        ( NTP4VCOffset p )
                        +
                        ( NTP4VCSigned32 D )
                      )
                    ) = (
                      NTP4VCPelts B
                      (
                        ( NTP4VCOffset B )
                        +
                        ( NTP4VCSigned32 D )
                      )
                    )
                  )
                  ->
                  (
                    NTP4VCCopyAfterWrite
                      p B C D E F G
                  )
                )
              )
          )
        )
      )
      \/
      (
        ( -. ( ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F ) ) )
        /\
        ( NTP4VCFinal A B C F G E )
      )
    )
  ) $.
$}

${
  $d i p A B C D E F G $.

  ntp4vc-copy-states-def $a |- (
    NTP4VCCopyStates A B C D E F G
  ) <-> (
    A. i e. NTP4VCWord32
      A. p e. ( NTP4VCPtr G )
        (
          ( NTP4VCSameMeta p A )
          ->
          (
            (
              NTP4VCCopyInvariant
                p B C i D E F
            )
            ->
            (
              NTP4VCCopyStep
                p B C i D E F G
            )
          )
        )
  ) $.
$}

ntp4vc-after-zero-test-def $a |- (
  NTP4VCAfterZeroTest A B C D E F G H I J
) <-> (
  (
    (
      I =/= 1
      /\
      (
        (
          NTP4VCCopyInvariant
            A B C E 0 G H
        )
        /\
        (
          NTP4VCCopyStates
            A B C 0 G H J
        )
      )
    )
    \/
    (
      I = 1
      /\
      (
        (
          0 <_ (
            ( NTP4VCSigned32 G )
            -
            ( NTP4VCSigned32 D )
          )
          /\
          (
            ( NTP4VCSigned32 G )
            -
            ( NTP4VCSigned32 E )
          ) < (
            ( NTP4VCSigned32 G )
            -
            ( NTP4VCSigned32 D )
          )
        )
        /\
        (
          NTP4VCBorrowInvariant
            A B C E F G H
        )
      )
    )
  )
) $.

${
  $d i o A B C D E F G H I $.

  ntp4vc-borrow-after-write-def $a |- (
    NTP4VCBorrowAfterWrite A B C D E F G H I
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) + 1 )
    )
    /\
    A. i e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 i
        ) = (
          ( NTP4VCSigned32 D ) + 1
        )
        ->
        A. o e. 2
          (
            ( NTP4VCBoolResult H o )
            ->
            (
              NTP4VCAfterZeroTest
                A B C D i E F G o I
            )
          )
      )
  ) $.
$}

${
  $d p A B C D E F G H I $.

  ntp4vc-borrow-write-def $a |- (
    NTP4VCBorrowWrite A B C D E F G H I
  ) <-> (
    A. p e. ( NTP4VCPtr I )
      (
        ( NTP4VCSameMeta p A )
        ->
        (
          (
            (
              NTP4VCUpdateLaw
                A p
                (
                  ( NTP4VCOffset p )
                  +
                  ( NTP4VCSigned32 D )
                )
                H
            )
            /\
            (
              NTP4VCPelts p
              (
                ( NTP4VCOffset p )
                +
                ( NTP4VCSigned32 D )
              )
            ) = H
          )
          ->
          (
            NTP4VCBorrowAfterWrite
              p B C D E F G
              (
                NTP4VCPelts B
                (
                  ( NTP4VCOffset B )
                  +
                  ( NTP4VCSigned32 D )
                )
              )
              I
          )
        )
      )
  ) $.
$}

${
  $d r A B C D E F G H $.

  ntp4vc-borrow-result-def $a |- (
    NTP4VCBorrowResult A B C D E F G H
  ) <-> (
    (
      NTP4VCBounds B ( NTP4VCSigned32 D )
    )
    /\
    A. r e. NTP4VCWord64
      (
        r = (
          (
            (
              NTP4VCPelts B
              (
                ( NTP4VCOffset B )
                +
                ( NTP4VCSigned32 D )
              )
            )
            -
            1
          )
          mod
          NTP4VCRadix
        )
        ->
        (
          (
            ( NTP4VCBounds A ( NTP4VCSigned32 D ) )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          (
            NTP4VCBorrowWrite
              A B C D E F G r H
          )
        )
      )
  ) $.
$}

ntp4vc-borrow-step-def $a |- (
  NTP4VCBorrowStep A B C D E F G H
) <-> (
  (
    (
      ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F )
      /\
      (
        NTP4VCBorrowResult
          A B C D E F G H
      )
    )
    \/
    (
      ( -. ( ( NTP4VCSigned32 D ) < ( NTP4VCSigned32 F ) ) )
      /\
      (
        (
          NTP4VCCopyInvariant
            A B C D E F G
        )
        /\
        (
          NTP4VCCopyStates
            A B C E F G H
        )
      )
    )
  )
) $.

${
  $d i b p A B C D E F $.

  ntp4vc-borrow-states-def $a |- (
    NTP4VCBorrowStates A B C D E F
  ) <-> (
    A. i e. NTP4VCWord32
      A. b e. NTP4VCWord64
        A. p e. ( NTP4VCPtr F )
          (
            ( NTP4VCSameMeta p A )
            ->
            (
              (
                NTP4VCBorrowInvariant
                  p B C i b D E
              )
              ->
              (
                NTP4VCBorrowStep
                  p B C i b D E F
              )
            )
          )
  ) $.
$}

ntp4vc-initial-borrow-def $a |- (
  NTP4VCInitialBorrow A B C D E F
) <-> (
  (
    NTP4VCBorrowInvariant
      A B C 1 1 D E
  )
  /\
  (
    NTP4VCBorrowStates
      A B C D E F
  )
) $.

ntp4vc-initial-copy-def $a |- (
  NTP4VCInitialCopy A B C D E F
) <-> (
  (
    NTP4VCCopyInvariant
      A B C 1 0 D E
  )
  /\
  (
    NTP4VCCopyStates
      A B C 0 D E F
  )
) $.

ntp4vc-after-first-write-def $a |- (
  NTP4VCAfterFirstWrite A B C D E F G
) <-> (
  (
    (
      F < E
      /\
      (
        NTP4VCInitialBorrow
          A B C D E G
      )
    )
    \/
    (
      ( -. ( F < E ) )
      /\
      (
        NTP4VCInitialCopy
          A B C D E G
      )
    )
  )
) $.

${
  $d p A B C D E F G $.

  ntp4vc-first-write-def $a |- (
    NTP4VCFirstWrite A B C D E F G
  ) <-> (
    A. p e. ( NTP4VCPtr G )
      (
        ( NTP4VCSameMeta p B )
        ->
        (
          (
            NTP4VCUpdateLaw
              B p ( NTP4VCOffset p ) F
          )
          ->
          (
            NTP4VCAfterFirstWrite
              p A B C D E G
          )
        )
      )
  ) $.
$}

${
  $d r A B C D E F $.

  ntp4vc-first-result-def $a |- (
    NTP4VCFirstResult A B C D E F
  ) <-> (
    A. r e. NTP4VCWord64
      (
        r = (
          (
            E
            -
            D
          )
          mod
          NTP4VCRadix
        )
        ->
        (
          (
            ( NTP4VCBounds B 0 )
            /\
            ( NTP4VCWritable B ) = 1
          )
          /\
          (
            NTP4VCFirstWrite
              A B C D E r F
          )
        )
      )
  ) $.
$}

ntp4vc-vc-def $a |- (
  NTP4VCVC A B C D E
) <-> (
  ( NTP4VCBounds A 0 )
  /\
  (
    NTP4VCFirstResult
      A B C D
      ( NTP4VCPelts A ( NTP4VCOffset A ) )
      E
  )
) $.

${
  $( Source parameters: A=x, B=sz, C=r, D=y, with common zone carrier Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-r-type $e |- C e. ( NTP4VCPtr Z ) $.
  ntp4vc-y-type $e |- D e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- (
    NTP4VCValid C ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact2 $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-fact3 $e |- ( NTP4VCWritable C ) = 1 $.

  ntp4vc-wmpn-sub-1-statement $a |- (
    NTP4VCVC A C B D Z
  ) $.
$}
