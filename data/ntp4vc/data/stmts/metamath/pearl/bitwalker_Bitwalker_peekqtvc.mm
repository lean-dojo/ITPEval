$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_peekqtvc: the bit-stream peek verification
  condition specifies the bounds, loop invariant, bit-copy update, and
  zero-padding behavior for reading at most 64 bits from a byte stream.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An n-bit word is represented exactly by its unsigned value in
  0 through 2^n-1. Thus zero extension is the identity, unsigned comparison
  is integer comparison, and fixed-width 32-bit addition and subtraction are
  integer operations modulo 2^32. A byte stream is an arbitrary finite SetMM
  word over the complete 8-bit carrier. NTP4VCAtByte is the source totalized
  list lookup, NTP4VCBit is totalized fixed-width bit extraction, and
  NTP4VCNth8Stream is the source byte-and-bit indexing operation.

  NTP4VCInvariant, NTP4VCFinish, and NTP4VCUpdate name, respectively, the
  loop invariant, the completed-read branch, and the bit-copy loop step in
  the joint Lean, Rocq, and Isabelle statement. NTP4VCLoopBody renders the
  proposition-valued conditional as its equivalent exhaustive guarded
  disjunction. NTP4VCPeekVC expands the outer conditional in the same way.
  Expanding these definitions recovers every source quantifier, implication,
  conjunction, bound check, bit equality, and zero-padding condition.

  The scoped essential hypotheses are bidirectionally equivalent to the
  source theorem's typed parameters and three assumptions. All integer,
  32-bit-word, 64-bit-word, and finite-byte-stream domains remain complete.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCByte NTP4VCWord32 NTP4VCWord64
  NTP4VCToNat NTP4VCAtByte NTP4VCBit NTP4VCNth8Stream
  NTP4VCAdd32 NTP4VCSub32
  NTP4VCInvariant NTP4VCFinish NTP4VCUpdate
  NTP4VCLoopBody NTP4VCPeekVC
$.

ntp4vc-byte-syntax $a class NTP4VCByte $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-byte-syntax $a class ( NTP4VCAtByte A B ) $.
ntp4vc-bit-syntax $a class ( NTP4VCBit A B C ) $.
ntp4vc-nth8-stream-syntax
  $a class ( NTP4VCNth8Stream A B ) $.
ntp4vc-add32-syntax $a class ( NTP4VCAdd32 A B ) $.
ntp4vc-sub32-syntax $a class ( NTP4VCSub32 A B ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C D ) $.
ntp4vc-update-syntax
  $a wff ( NTP4VCUpdate A B C D E ) $.
ntp4vc-loop-body-syntax
  $a wff ( NTP4VCLoopBody A B C D E ) $.
ntp4vc-peek-vc-syntax
  $a wff ( NTP4VCPeekVC A B C ) $.

ntp4vc-byte-definition $a |- NTP4VCByte =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-byte-definition $a |- (
  NTP4VCAtByte A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-bit-definition $a |- (
  NTP4VCBit A B C
) = if (
  ( NTP4VCToNat B ) < C ,
  (
    (
      |_ ` (
        A / ( 2 ^ ( NTP4VCToNat B ) )
      )
    )
    mod
    2
  ) ,
  0
) $.

ntp4vc-nth8-stream-definition $a |- (
  NTP4VCNth8Stream A B
) = (
  NTP4VCBit
    (
      NTP4VCAtByte
        A
        ( |_ ` ( B / 8 ) )
    )
    ( 7 - ( B mod 8 ) )
    8
) $.

ntp4vc-add32-definition $a |- (
  NTP4VCAdd32 A B
) = (
  ( A + B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-sub32-definition $a |- (
  NTP4VCSub32 A B
) = (
  ( A - B ) mod ( 2 ^ ; 3 2 )
) $.

${
  $d j A $.  $d j B $.  $d j C $.  $d j D $.  $d j E $.

  ntp4vc-invariant-definition $a |- (
    NTP4VCInvariant A B C D E
  ) <-> (
    (
      0 <_ D
      /\
      D <_ A
    )
    /\
    (
      A. j e. ZZ
        (
          (
            ( A - D ) <_ j
            /\
            j < A
          )
          ->
          (
            NTP4VCBit E j ; 6 4
          )
          =
          (
            NTP4VCNth8Stream
              C
              ( ( ( B + A ) - j ) - 1 )
          )
        )
      /\
      (
        A. j e. ZZ
          (
            (
              0 <_ j
              /\
              j < ( A - D )
            )
            ->
            ( NTP4VCBit E j ; 6 4 ) = 0
          )
        /\
        A. j e. ZZ
          (
            (
              A <_ j
              /\
              j < ; 6 4
            )
            ->
            ( NTP4VCBit E j ; 6 4 ) = 0
          )
      )
    )
  ) $.
$}

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.

  ntp4vc-finish-definition $a |- (
    NTP4VCFinish A B C D
  ) <-> (
    (
      (
        ( 8 x. ( # ` C ) )
        <
        ( B + A )
      )
      ->
      D = 0
    )
    /\
    (
      (
        ( B + A )
        <_
        ( 8 x. ( # ` C ) )
      )
      ->
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < A
            )
            ->
            (
              NTP4VCBit D i ; 6 4
            )
            =
            (
              NTP4VCNth8Stream
                C
                ( ( ( B + A ) - i ) - 1 )
            )
          )
        /\
        A. i e. ZZ
          (
            (
              A <_ i
              /\
              i < ; 6 4
            )
            ->
            ( NTP4VCBit D i ; 6 4 ) = 0
          )
      )
    )
  ) $.
$}

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.  $d i E $.
  $d o A $.  $d o B $.  $d o C $.  $d o D $.  $d o E $.

  ntp4vc-update-definition $a |- (
    NTP4VCUpdate A B C D E
  ) <-> (
    (
      (
        ( B + D ) < ; 4 2 9 4 9 6 7 2 9 6
        \/
        ( B + D ) <_ ; 4 2 9 4 9 6 7 2 9 5
      )
      /\
      (
        (
          ( NTP4VCAdd32 B D ) = ( B + D )
        )
        ->
        (
          (
            (
              ( 8 x. ( # ` C ) )
              <
              ; 4 2 9 4 9 6 7 2 9 6
            )
            /\
            (
              ( NTP4VCAdd32 B D )
              <
              ( 8 x. ( # ` C ) )
            )
          )
          /\
          (
            (
              (
                ( ( NTP4VCSub32 ; 6 4 A ) + D )
                <
                ; 4 2 9 4 9 6 7 2 9 6
              )
              \/
              (
                ( ( NTP4VCSub32 ; 6 4 A ) + D )
                <_
                ; 4 2 9 4 9 6 7 2 9 5
              )
            )
            /\
            (
              (
                ( NTP4VCAdd32
                    ( NTP4VCSub32 ; 6 4 A )
                    D
                )
                =
                ( ( NTP4VCSub32 ; 6 4 A ) + D )
              )
              ->
              (
                (
                  NTP4VCAdd32
                    ( NTP4VCSub32 ; 6 4 A )
                    D
                )
                <
                ; 6 4
                /\
                A. o e. NTP4VCWord64
                  (
                    (
                      A. i e. ZZ
                        (
                          (
                            (
                              0 <_ i
                              /\
                              i < ; 6 4
                            )
                            /\
                            i =/=
                            (
                              ; 6 3
                              -
                              (
                                NTP4VCAdd32
                                  ( NTP4VCSub32 ; 6 4 A )
                                  D
                              )
                            )
                          )
                          ->
                          (
                            NTP4VCBit o i ; 6 4
                          )
                          =
                          (
                            NTP4VCBit E i ; 6 4
                          )
                        )
                      /\
                      (
                        NTP4VCNth8Stream
                          C
                          ( NTP4VCAdd32 B D )
                      )
                      =
                      (
                        NTP4VCBit
                          o
                          (
                            ; 6 3
                            -
                            (
                              NTP4VCAdd32
                                ( NTP4VCSub32 ; 6 4 A )
                                D
                            )
                          )
                          ; 6 4
                      )
                    )
                    ->
                    (
                      (
                        ( D + 1 )
                        <
                        ; 4 2 9 4 9 6 7 2 9 6
                        \/
                        ( D + 1 )
                        <_
                        ; 4 2 9 4 9 6 7 2 9 5
                      )
                      /\
                      (
                        (
                          ( NTP4VCAdd32 D 1 )
                          =
                          ( D + 1 )
                        )
                        ->
                        (
                          (
                            0 <_ ( A - D )
                            /\
                            (
                              A - ( NTP4VCAdd32 D 1 )
                            )
                            <
                            ( A - D )
                          )
                          /\
                          (
                            NTP4VCInvariant
                              A B C
                              ( NTP4VCAdd32 D 1 )
                              o
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

ntp4vc-loop-body-definition $a |- (
  NTP4VCLoopBody A B C D E
) <-> (
  (
    D < A
    /\
    ( NTP4VCUpdate A B C D E )
  )
  \/
  (
    -. D < A
    /\
    ( NTP4VCFinish A B C E )
  )
) $.

${
  $d i A $.  $d i B $.  $d i C $.
  $d r A $.  $d r B $.  $d r C $.  $d r i $.

  ntp4vc-peek-vc-definition $a |- (
    NTP4VCPeekVC A B C
  ) <-> (
    (
      ( B + A ) < ; 4 2 9 4 9 6 7 2 9 6
      \/
      ( B + A ) <_ ; 4 2 9 4 9 6 7 2 9 5
    )
    /\
    (
      (
        ( NTP4VCAdd32 B A ) = ( B + A )
      )
      ->
      (
        (
          (
            ( 8 x. ( # ` C ) )
            <
            ( NTP4VCAdd32 B A )
          )
          /\
          (
            (
              ( B + A )
              <_
              ( 8 x. ( # ` C ) )
            )
            ->
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < A
                  )
                  ->
                  (
                    NTP4VCBit 0 i ; 6 4
                  )
                  =
                  (
                    NTP4VCNth8Stream
                      C
                      ( ( ( B + A ) - i ) - 1 )
                  )
                )
              /\
              A. i e. ZZ
                (
                  (
                    A <_ i
                    /\
                    i < ; 6 4
                  )
                  ->
                  ( NTP4VCBit 0 i ; 6 4 ) = 0
                )
            )
          )
        )
        \/
        (
          -.
          (
            ( 8 x. ( # ` C ) )
            <
            ( NTP4VCAdd32 B A )
          )
          /\
          (
            (
              A <_ ; 6 4
              \/
              A <_ ; 6 4
            )
            /\
            (
              (
                ( NTP4VCSub32 ; 6 4 A )
                =
                ( ; 6 4 - A )
              )
              ->
              (
                ( NTP4VCInvariant A B C 0 0 )
                /\
                A. i e. NTP4VCWord32
                  A. r e. NTP4VCWord64
                    (
                      ( NTP4VCInvariant A B C i r )
                      ->
                      ( NTP4VCLoopBody A B C i r )
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
  $( Source parameters: A=len, B=start, and C=addr. $)

  ntp4vc-len-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-start-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-addr-byte-stream $e |- C e. Word NTP4VCByte $.

  ntp4vc-len-at-most-64 $e |- A <_ ; 6 4 $.
  ntp4vc-start-plus-len-in-range
    $e |- ( B + A ) < ; 4 2 9 4 9 6 7 2 9 6 $.
  ntp4vc-stream-bit-length-in-range
    $e |- ( 8 x. ( # ` C ) ) < ; 4 2 9 4 9 6 7 2 9 6 $.

  ntp4vc-pearl-bitwalker-peek-vc $a |- (
    NTP4VCPeekVC A B C
  ) $.
$}
