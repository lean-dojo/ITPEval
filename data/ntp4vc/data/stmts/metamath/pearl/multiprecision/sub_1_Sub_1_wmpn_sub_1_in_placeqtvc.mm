$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1_in_placeqtvc: the verification
  condition for subtracting a 64-bit limb from a nonempty writable
  multiprecision unsigned integer in place, including modular limb updates,
  borrow propagation, loop invariants, pointer metadata, and memory framing.
  This file contains no proof.

  Unsigned 32- and 64-bit words use their complete canonical integer
  carriers, with exact two's-complement signed interpretation for 32-bit
  indices. Pointer data are finite 64-bit limb sequences; integer indexing
  uses the source Int.toNat behavior and a zero default outside the sequence.
  The predicates below are definitional factorizations of the source
  validity, positional value, functional-update, frame, invariant, branch,
  and continuation formulas. Expanding them yields the original nested
  verification condition.
$)

$[ lib/set.mm $]

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32 NTP4VCInt32InBounds
  NTP4VCRadix NTP4VCPtr NTP4VCData NTP4VCLength NTP4VCOffset
  NTP4VCMin NTP4VCMax NTP4VCWritable NTP4VCZone NTP4VCToNat
  NTP4VCPelts NTP4VCValid NTP4VCValue NTP4VCSameMeta
  NTP4VCUpdateLaw NTP4VCBounds NTP4VCOutsideFrame
  NTP4VCBoolResult NTP4VCFinal NTP4VCLoopInvariant
  NTP4VCNextInvariant NTP4VCAfterBoolean NTP4VCAfterIncrement
  NTP4VCSecondWrite NTP4VCSecondResult NTP4VCLoopStep
  NTP4VCLoopStates NTP4VCInitialState NTP4VCFirstBranch
  NTP4VCFirstWrite NTP4VCFirstResult NTP4VCVC
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
ntp4vc-final-syn $a wff ( NTP4VCFinal A B C D E ) $.
ntp4vc-loop-invariant-syn
  $a wff ( NTP4VCLoopInvariant A B C D E F ) $.
ntp4vc-next-invariant-syn
  $a wff ( NTP4VCNextInvariant A B C D E F G ) $.
ntp4vc-after-boolean-syn
  $a wff ( NTP4VCAfterBoolean A B C D E F G H ) $.
ntp4vc-after-increment-syn
  $a wff ( NTP4VCAfterIncrement A B C D E F G ) $.
ntp4vc-second-write-syn
  $a wff ( NTP4VCSecondWrite A B C D E F G H ) $.
ntp4vc-second-result-syn
  $a wff ( NTP4VCSecondResult A B C D E F G ) $.
ntp4vc-loop-step-syn
  $a wff ( NTP4VCLoopStep A B C D E F G ) $.
ntp4vc-loop-states-syn
  $a wff ( NTP4VCLoopStates A B C D E ) $.
ntp4vc-initial-state-syn
  $a wff ( NTP4VCInitialState A B C D ) $.
ntp4vc-first-branch-syn
  $a wff ( NTP4VCFirstBranch A B C D E F ) $.
ntp4vc-first-write-syn
  $a wff ( NTP4VCFirstWrite A B C D E F ) $.
ntp4vc-first-result-syn
  $a wff ( NTP4VCFirstResult A B C D ) $.
ntp4vc-vc-syn $a wff ( NTP4VCVC A B C D ) $.

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
  ( Word NTP4VCWord64 )
  X.
  ( ZZ X. ( ZZ X. ( ZZ X. ( { 0 , 1 } X. A ) ) ) )
) $.

ntp4vc-data-def $a |- (
  NTP4VCData A
) = ( 1st ` A ) $.

ntp4vc-length-def $a |- (
  NTP4VCLength A
) = ( # ` ( NTP4VCData A ) ) $.

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
) = if (
  ( NTP4VCToNat B ) < ( NTP4VCLength A ) ,
  ( ( NTP4VCData A ) ` ( NTP4VCToNat B ) ) ,
  0
) $.

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

ntp4vc-final-def $a |- (
  NTP4VCFinal A B C D E
) <-> (
  (
    (
      ( NTP4VCValue A ( NTP4VCSigned32 C ) )
      -
      (
        (
          NTP4VCRadix
          ^
          ( NTP4VCToNat ( NTP4VCSigned32 C ) )
        )
        x.
        E
      )
    ) = (
      ( NTP4VCValue B ( NTP4VCSigned32 C ) )
      -
      D
    )
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
      NTP4VCOutsideFrame
        A B ( NTP4VCSigned32 C )
    )
  )
) $.

ntp4vc-loop-invariant-def $a |- (
  NTP4VCLoopInvariant A B C D E F
) <-> (
  (
    1 <_ ( NTP4VCSigned32 B )
    /\
    ( NTP4VCSigned32 B ) <_ ( NTP4VCSigned32 E )
  )
  /\
  (
    (
      0 <_ C
      /\
      C <_ 1
    )
    /\
    (
      (
        C = 1
        \/
        B = E
      )
      /\
      (
        (
          (
            NTP4VCValue A ( NTP4VCSigned32 B )
          )
          -
          (
            (
              NTP4VCRadix
              ^
              ( NTP4VCToNat ( NTP4VCSigned32 B ) )
            )
            x.
            C
          )
        ) = (
          (
            NTP4VCValue D ( NTP4VCSigned32 B )
          )
          -
          F
        )
        /\
        (
          NTP4VCOutsideFrame
            A D ( NTP4VCSigned32 B )
        )
      )
    )
  )
) $.

ntp4vc-next-invariant-def $a |- (
  NTP4VCNextInvariant A B C D E F G
) <-> (
  (
    0 <_ (
      ( NTP4VCSigned32 F )
      -
      ( NTP4VCSigned32 B )
    )
    /\
    (
      ( NTP4VCSigned32 F )
      -
      ( NTP4VCSigned32 C )
    ) < (
      ( NTP4VCSigned32 F )
      -
      ( NTP4VCSigned32 B )
    )
  )
  /\
  (
    NTP4VCLoopInvariant A C D E F G
  )
) $.

${
  $d o A B C D E F G H $.

  ntp4vc-after-boolean-def $a |- (
    NTP4VCAfterBoolean A B C D E F G H
  ) <-> (
    A. o e. { 0 , 1 }
      (
        ( NTP4VCBoolResult B o )
        ->
        (
          (
            o =/= 1
            /\
            ( NTP4VCFinal A C F G 0 )
          )
          \/
          (
            o = 1
            /\
            (
              NTP4VCNextInvariant
                A D E H C F G
            )
          )
        )
      )
  ) $.
$}

${
  $d r A B C D E F G H $.

  ntp4vc-after-increment-def $a |- (
    NTP4VCAfterIncrement A B C D E F G
  ) <-> (
    (
      NTP4VCInt32InBounds
        ( ( NTP4VCSigned32 D ) + 1 )
    )
    /\
    A. r e. NTP4VCWord32
      (
        (
          NTP4VCSigned32 r
        ) = (
          ( NTP4VCSigned32 D ) + 1
        )
        ->
        (
          NTP4VCAfterBoolean
            A
            ( NTP4VCPelts
              B
              (
                ( NTP4VCOffset B )
                +
                ( NTP4VCSigned32 D )
              )
            )
            C D r F G E
        )
      )
  ) $.
$}

${
  $d p A B C D E F G H I $.

  ntp4vc-second-write-def $a |- (
    NTP4VCSecondWrite A B C D E F G H
  ) <-> (
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
                  ( NTP4VCSigned32 C )
                )
                G
            )
            /\
            (
              NTP4VCPelts
                p
                (
                  ( NTP4VCOffset p )
                  +
                  ( NTP4VCSigned32 C )
                )
            ) = G
          )
          ->
          (
            NTP4VCAfterIncrement
              p A B C D E F
          )
        )
      )
  ) $.
$}

${
  $d r A B C D E F G H $.

  ntp4vc-second-result-def $a |- (
    NTP4VCSecondResult A B C D E F G
  ) <-> (
    ( NTP4VCBounds A ( NTP4VCSigned32 C ) )
    /\
    A. r e. NTP4VCWord64
      (
        r = (
          (
            (
              NTP4VCPelts
                A
                (
                  ( NTP4VCOffset A )
                  +
                  ( NTP4VCSigned32 C )
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
            ( NTP4VCBounds A ( NTP4VCSigned32 C ) )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          (
            NTP4VCSecondWrite
              A B C D E F r G
          )
        )
      )
  ) $.
$}

ntp4vc-loop-step-def $a |- (
  NTP4VCLoopStep A B C D E F G
) <-> (
  (
    (
      ( NTP4VCSigned32 B ) < ( NTP4VCSigned32 E )
      /\
      (
        NTP4VCSecondResult A D B C E F G
      )
    )
    \/
    (
      ( -. ( ( NTP4VCSigned32 B ) < ( NTP4VCSigned32 E ) ) )
      /\
      ( NTP4VCFinal A D E F C )
    )
  )
) $.

${
  $d i b p A B C D E $.

  ntp4vc-loop-states-def $a |- (
    NTP4VCLoopStates A B C D E
  ) <-> (
    A. i e. NTP4VCWord32
      A. b e. NTP4VCWord64
        A. p e. ( NTP4VCPtr E )
          (
            ( NTP4VCSameMeta p A )
            ->
            (
              (
                NTP4VCLoopInvariant p i b B C D
              )
              ->
              (
                NTP4VCLoopStep p i b B C D E
              )
            )
          )
  ) $.
$}

ntp4vc-initial-state-def $a |- (
  NTP4VCInitialState A B C D
) <-> (
  (
    1 <_ 1
    /\
    1 <_ ( NTP4VCSigned32 C )
  )
  /\
  (
    (
      0 <_ 1
      /\
      1 <_ 1
    )
    /\
    (
      (
        1 = 1
        \/
        1 = C
      )
      /\
      (
        (
          (
            ( NTP4VCValue A 1 )
            -
            ( ( NTP4VCRadix ^ 1 ) x. 1 )
          ) = (
            ( NTP4VCValue B 1 )
            -
            D
          )
        )
        /\
        ( NTP4VCOutsideFrame A B 1 )
      )
    )
  )
) $.

ntp4vc-first-branch-def $a |- (
  NTP4VCFirstBranch A B C D E F
) <-> (
  (
    (
      E < D
      /\
      (
        ( NTP4VCInitialState A B C D )
        /\
        ( NTP4VCLoopStates A B C D F )
      )
    )
    \/
    (
      ( -. ( E < D ) )
      /\
      ( NTP4VCFinal A B C D 0 )
    )
  )
) $.

${
  $d p A B C D E F $.

  ntp4vc-first-write-def $a |- (
    NTP4VCFirstWrite A B C D E F
  ) <-> (
    A. p e. ( NTP4VCPtr F )
      (
        ( NTP4VCSameMeta p A )
        ->
        (
          (
            NTP4VCUpdateLaw
              A p ( NTP4VCOffset p ) D
          )
          ->
          (
            NTP4VCFirstBranch
              p A B C E F
          )
        )
      )
  ) $.
$}

${
  $d r A B C D $.

  ntp4vc-first-result-def $a |- (
    NTP4VCFirstResult A B C D
  ) <-> (
    A. r e. NTP4VCWord64
      (
        r = (
          (
            ( NTP4VCPelts A ( NTP4VCOffset A ) )
            -
            C
          )
          mod
          NTP4VCRadix
        )
        ->
        (
          (
            ( NTP4VCBounds A 0 )
            /\
            ( NTP4VCWritable A ) = 1
          )
          /\
          (
            NTP4VCFirstWrite
              A B C r
              ( NTP4VCPelts A ( NTP4VCOffset A ) )
              D
          )
        )
      )
  ) $.
$}

ntp4vc-vc-def $a |- (
  NTP4VCVC A B C D
) <-> (
  ( NTP4VCBounds A 0 )
  /\
  ( NTP4VCFirstResult A B C D )
) $.

${
  $( Source parameters: A=x, B=sz, C=y, with common zone carrier Z. $)

  ntp4vc-zone-set $e |- Z e. _V $.
  ntp4vc-zone-nonempty $e |- Z =/= (/) $.
  ntp4vc-x-type $e |- A e. ( NTP4VCPtr Z ) $.
  ntp4vc-sz-type $e |- B e. NTP4VCWord32 $.
  ntp4vc-y-type $e |- C e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- (
    NTP4VCValid A ( NTP4VCSigned32 B )
  ) $.
  ntp4vc-fact1 $e |- 0 < ( NTP4VCSigned32 B ) $.
  ntp4vc-fact2 $e |- ( NTP4VCWritable A ) = 1 $.

  ntp4vc-wmpn-sub-1-in-place-statement $a |- (
    NTP4VCVC A B C Z
  ) $.
$}
