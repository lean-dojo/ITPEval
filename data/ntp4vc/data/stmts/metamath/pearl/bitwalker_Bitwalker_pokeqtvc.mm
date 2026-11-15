$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokeqtvc: the bit-stream poke verification
  condition specifies overflow checks, return-code cases, the loop invariant,
  one-bit stream updates, and preservation outside the written interval while
  writing at most 64 bits into a byte stream. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An n-bit word is represented exactly by its unsigned integer value in
  0 through 2^n-1, and a byte stream is an arbitrary finite SetMM word over
  the complete 8-bit carrier. NTP4VCAtByte is the source totalized list
  lookup, NTP4VCBit is totalized fixed-width extraction after Int.toNat
  conversion, and NTP4VCNth8Stream reproduces the source byte-and-bit
  indexing operation.

  NTP4VCAdd32 and NTP4VCSub32 are fixed-width operations modulo 2^32.
  NTP4VCMaxValue is the unsigned value of the source 64-bit left shift of
  one by the zero-extended 32-bit length. Zero extension to 128 bits is the
  identity on these unsigned carriers, so NTP4VCOverflow32 states both
  disjuncts of each source overflow check directly over integers.

  NTP4VCInit, NTP4VCInvariant, NTP4VCStep, and NTP4VCFinal name exactly the
  loop initialization, arbitrary-state invariant premise, one-bit update
  branch, and completed-write branch. NTP4VCPokeVC renders each
  proposition-valued conditional as an exhaustive guarded disjunction.
  Expanding the definitions recovers every source quantifier, implication,
  conjunction, bound, bit equality, same-length condition, return-code
  equivalence, and fixed-width operation.

  The scoped essential hypotheses are bidirectionally equivalent to the
  source theorem's four typed parameters and three assumptions. All integer,
  8-bit-word, 32-bit-word, 64-bit-word, and finite-byte-stream domains remain
  complete. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCByte NTP4VCWord32 NTP4VCWord64
  NTP4VCToNat NTP4VCAtByte NTP4VCBit NTP4VCNth8Stream
  NTP4VCAdd32 NTP4VCSub32 NTP4VCMaxValue NTP4VCOverflow32
  NTP4VCInit NTP4VCInvariant NTP4VCStep NTP4VCFinal NTP4VCPokeVC
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
ntp4vc-max-value-syntax $a class ( NTP4VCMaxValue A ) $.
ntp4vc-overflow32-syntax
  $a wff ( NTP4VCOverflow32 A B ) $.
ntp4vc-init-syntax
  $a wff ( NTP4VCInit A B C D ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B C D E F ) $.
ntp4vc-poke-vc-syntax
  $a wff ( NTP4VCPokeVC A B C D ) $.

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

ntp4vc-max-value-definition $a |- (
  NTP4VCMaxValue A
) = (
  ( 2 ^ A ) mod ( 2 ^ ; 6 4 )
) $.

ntp4vc-overflow32-definition $a |- (
  NTP4VCOverflow32 A B
) <-> (
  (
    ( A + B ) < ; 4 2 9 4 9 6 7 2 9 6
  )
  \/
  (
    ( A + B ) <_ ; 4 2 9 4 9 6 7 2 9 5
  )
) $.

${
  $d j A $.  $d j B $.  $d j C $.  $d j D $.

  ntp4vc-init-definition $a |- (
    NTP4VCInit A B C D
  ) <-> (
    (
      0 <_ 0
      /\
      0 <_ A
    )
    /\
    A. j e. ZZ
      (
        (
          B <_ j
          /\
          j < ( B + 0 )
        )
        ->
        (
          NTP4VCNth8Stream C j
        )
        =
        (
          NTP4VCBit
            D
            ( ( ( A - j ) - 1 ) + B )
            ; 6 4
        )
      )
  ) $.
$}

${
  $d j A $.  $d j B $.  $d j C $.
  $d j D $.  $d j E $.  $d j F $.

  ntp4vc-invariant-definition $a |- (
    NTP4VCInvariant A B C D E F
  ) <-> (
    (
      0 <_ E
      /\
      E <_ A
    )
    /\
    (
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < B
          )
          ->
          (
            NTP4VCNth8Stream C j
          )
          =
          (
            NTP4VCNth8Stream F j
          )
        )
      /\
      (
        A. j e. ZZ
          (
            (
              B <_ j
              /\
              j < ( B + E )
            )
            ->
            (
              NTP4VCNth8Stream F j
            )
            =
            (
              NTP4VCBit
                D
                ( ( ( A - j ) - 1 ) + B )
                ; 6 4
            )
          )
        /\
        A. j e. ZZ
          (
            (
              ( B + E ) <_ j
              /\
              j < ( 8 x. ( # ` F ) )
            )
            ->
            (
              NTP4VCNth8Stream F j
            )
            =
            (
              NTP4VCNth8Stream C j
            )
          )
      )
    )
  ) $.
$}

${
  $d g A $.  $d g B $.  $d g C $.
  $d g D $.  $d g E $.  $d g F $.
  $d h A $.  $d h B $.  $d h C $.
  $d h D $.  $d h E $.  $d h F $.  $d h g $.

  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E F
  ) <-> (
    (
      NTP4VCOverflow32
        ( NTP4VCSub32 ; 6 4 A )
        E
    )
    /\
    (
      (
        (
          NTP4VCAdd32
            ( NTP4VCSub32 ; 6 4 A )
            E
        )
        =
        (
          ( NTP4VCSub32 ; 6 4 A ) + E
        )
      )
      ->
      (
        (
          NTP4VCAdd32
            ( NTP4VCSub32 ; 6 4 A )
            E
        )
        <
        ; 6 4
      )
      /\
      (
        ( NTP4VCOverflow32 B E )
        /\
        (
          (
            ( NTP4VCAdd32 B E ) = ( B + E )
          )
          ->
          (
            (
              ( 8 x. ( # ` F ) )
              <
              ; 4 2 9 4 9 6 7 2 9 6
            )
            /\
            (
              ( NTP4VCAdd32 B E )
              <
              ( 8 x. ( # ` F ) )
            )
          )
          /\
          A. g e. Word NTP4VCByte
            (
              ( # ` g ) = ( # ` F )
              ->
              (
                (
                  A. h e. ZZ
                    (
                      (
                        (
                          0 <_ h
                          /\
                          h < ( 8 x. ( # ` g ) )
                        )
                        /\
                        h =/= ( NTP4VCAdd32 B E )
                      )
                      ->
                      (
                        NTP4VCNth8Stream g h
                      )
                      =
                      (
                        NTP4VCNth8Stream F h
                      )
                    )
                  /\
                  (
                    NTP4VCNth8Stream
                      g
                      ( NTP4VCAdd32 B E )
                  )
                  =
                  (
                    NTP4VCBit
                      D
                      (
                        ; 6 3
                        -
                        (
                          NTP4VCAdd32
                            ( NTP4VCSub32 ; 6 4 A )
                            E
                        )
                      )
                      ; 6 4
                  )
                )
                ->
                (
                  ( NTP4VCOverflow32 E 1 )
                  /\
                  (
                    (
                      ( NTP4VCAdd32 E 1 )
                      =
                      ( E + 1 )
                    )
                    ->
                    (
                      (
                        0 <_ ( A - E )
                        /\
                        (
                          A - ( NTP4VCAdd32 E 1 )
                        )
                        <
                        ( A - E )
                      )
                      /\
                      (
                        NTP4VCInvariant
                          A B C D
                          ( NTP4VCAdd32 E 1 )
                          g
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
  $d h A $.  $d h B $.  $d h C $.
  $d h D $.  $d h E $.  $d h F $.

  ntp4vc-final-definition $a |- (
    NTP4VCFinal A B C D E F
  ) <-> (
    (
      ( -u 2 ) <_ 0
      /\
      0 <_ 0
    )
    /\
    (
      (
        0 = ( -u 1 )
        <->
        (
          ( 8 x. ( # ` F ) )
          <
          ( B + A )
        )
      )
      /\
      (
        (
          0 = ( -u 2 )
          <->
          (
            ( NTP4VCMaxValue A ) <_ D
            /\
            (
              ( B + A )
              <_
              ( 8 x. ( # ` F ) )
            )
          )
        )
        /\
        (
          D < ( NTP4VCMaxValue A )
          /\
          (
            ( B + A )
            <_
            ( 8 x. ( # ` F ) )
          )
        )
      )
    )
    /\
    (
      A. h e. ZZ
        (
          (
            0 <_ h
            /\
            h < B
          )
          ->
          (
            NTP4VCNth8Stream C h
          )
          =
          (
            NTP4VCNth8Stream F h
          )
        )
      /\
      (
        A. h e. ZZ
          (
            (
              B <_ h
              /\
              h < ( B + A )
            )
            ->
            (
              NTP4VCNth8Stream F h
            )
            =
            (
              NTP4VCBit
                D
                ( ( ( A - h ) - 1 ) + B )
                ; 6 4
            )
          )
        /\
        A. h e. ZZ
          (
            (
              ( B + A ) <_ h
              /\
              h < ( 8 x. ( # ` F ) )
            )
            ->
            (
              NTP4VCNth8Stream F h
            )
            =
            (
              NTP4VCNth8Stream C h
            )
          )
      )
    )
  ) $.
$}

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.
  $d f A $.  $d f B $.  $d f C $.  $d f D $.  $d f i $.

  ntp4vc-poke-vc-definition $a |- (
    NTP4VCPokeVC A B C D
  ) <-> (
    ( NTP4VCOverflow32 B A )
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
              ( -u 2 ) <_ ( -u 1 )
              /\
              ( -u 1 ) <_ 0
            )
            /\
            (
              ( 8 x. ( # ` C ) )
              <
              ( B + A )
            )
            /\
            (
              (
                ( -u 1 ) = ( -u 2 )
                <->
                (
                  ( NTP4VCMaxValue A ) <_ D
                  /\
                  (
                    ( B + A )
                    <_
                    ( 8 x. ( # ` C ) )
                  )
                )
              )
              /\
              (
                (
                  ( -u 1 ) = 0
                  <->
                  (
                    D < ( NTP4VCMaxValue A )
                    /\
                    (
                      ( B + A )
                      <_
                      ( 8 x. ( # ` C ) )
                    )
                  )
                )
                /\
                (
                  ( -u 1 ) = 0
                  ->
                  A. i e. ZZ
                    (
                      (
                        B <_ i
                        /\
                        i < ( B + A )
                      )
                      ->
                      (
                        NTP4VCNth8Stream C i
                      )
                      =
                      (
                        NTP4VCBit
                          D
                          ( ( ( A - i ) - 1 ) + B )
                          ; 6 4
                      )
                    )
                )
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
              ( NTP4VCMaxValue A ) <_ D
              /\
              (
                (
                  ( -u 2 ) <_ ( -u 2 )
                  /\
                  ( -u 2 ) <_ 0
                )
                /\
                (
                  (
                    ( -u 2 ) = ( -u 1 )
                    <->
                    (
                      ( 8 x. ( # ` C ) )
                      <
                      ( B + A )
                    )
                  )
                  /\
                  (
                    ( NTP4VCMaxValue A ) <_ D
                    /\
                    (
                      ( B + A )
                      <_
                      ( 8 x. ( # ` C ) )
                    )
                  )
                )
                /\
                (
                  (
                    ( -u 2 ) = 0
                    <->
                    (
                      D < ( NTP4VCMaxValue A )
                      /\
                      (
                        ( B + A )
                        <_
                        ( 8 x. ( # ` C ) )
                      )
                    )
                  )
                  /\
                  (
                    ( -u 2 ) = 0
                    ->
                    A. i e. ZZ
                      (
                        (
                          B <_ i
                          /\
                          i < ( B + A )
                        )
                        ->
                        (
                          NTP4VCNth8Stream C i
                        )
                        =
                        (
                          NTP4VCBit
                            D
                            ( ( ( A - i ) - 1 ) + B )
                            ; 6 4
                        )
                      )
                  )
                )
              )
            )
            \/
            (
              -.
              ( ( NTP4VCMaxValue A ) <_ D )
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
                    ( NTP4VCInit A B C D )
                    /\
                    A. i e. NTP4VCWord32
                      A. f e. Word NTP4VCByte
                        (
                          ( # ` f ) = ( # ` C )
                          ->
                          (
                            (
                              NTP4VCInvariant
                                A B C D i f
                            )
                            ->
                            (
                              (
                                i < A
                                /\
                                (
                                  NTP4VCStep
                                    A B C D i f
                                )
                              )
                              \/
                              (
                                -. i < A
                                /\
                                (
                                  NTP4VCFinal
                                    A B C D i f
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
  $( Source parameters: A=len, B=start, C=addr, and D=value. $)

  ntp4vc-len-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-start-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-addr-byte-stream $e |- C e. Word NTP4VCByte $.
  ntp4vc-value-word64 $e |- D e. NTP4VCWord64 $.

  ntp4vc-len-less-than-64 $e |- A < ; 6 4 $.
  ntp4vc-start-plus-len-in-range
    $e |- ( B + A ) < ; 4 2 9 4 9 6 7 2 9 6 $.
  ntp4vc-stream-bit-length-in-range
    $e |- ( 8 x. ( # ` C ) ) < ; 4 2 9 4 9 6 7 2 9 6 $.

  ntp4vc-pearl-bitwalker-poke-vc $a |- (
    NTP4VCPokeVC A B C D
  ) $.
$}
