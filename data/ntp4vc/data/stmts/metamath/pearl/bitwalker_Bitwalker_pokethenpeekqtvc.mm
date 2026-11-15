$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokethenpeekqtvc: the bit-stream poke-then-peek
  verification condition specifies return-code cases for writing at most
  64 bits, preservation outside the written interval, and recovery of the
  written 64-bit value by a subsequent bounded read. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  An n-bit word is represented exactly by its unsigned integer value in
  0 through 2^n-1. A byte stream is an arbitrary finite SetMM word over the
  complete 8-bit carrier. NTP4VCAtByte is the source totalized list lookup,
  NTP4VCBit is totalized fixed-width bit extraction, and
  NTP4VCNth8Stream is the source byte-and-bit indexing operation. Boolean
  bits are represented by 0 and 1, so source equality with false is equality
  with 0.

  NTP4VCMaxValue is the unsigned value of the source 64-bit left shift of
  one by the zero-extended 32-bit length. NTP4VCPokeSpec reproduces the
  return-code range, all three return-code equivalences, and the conditional
  preservation and bit-update clauses. NTP4VCReadSpec reproduces the
  out-of-range zero result and the in-range bit-copy and zero-padding
  clauses. Expanding these definitions recovers every source quantifier,
  implication, conjunction, bound, bit equality, and same-length condition.

  The scoped essential hypotheses are bidirectionally equivalent to the
  source theorem's four typed parameters and five assumptions. All integer,
  8-bit-word, 32-bit-word, 64-bit-word, and finite-byte-stream domains remain
  complete. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCByte NTP4VCWord32 NTP4VCWord64
  NTP4VCToNat NTP4VCAtByte NTP4VCBit NTP4VCNth8Stream
  NTP4VCMaxValue NTP4VCReadSpec NTP4VCPokeSpec
$.

ntp4vc-byte-syntax $a class NTP4VCByte $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-byte-syntax $a class ( NTP4VCAtByte A B ) $.
ntp4vc-bit-syntax $a class ( NTP4VCBit A B C ) $.
ntp4vc-nth8-stream-syntax
  $a class ( NTP4VCNth8Stream A B ) $.
ntp4vc-max-value-syntax $a class ( NTP4VCMaxValue A ) $.
ntp4vc-read-spec-syntax
  $a wff ( NTP4VCReadSpec A B C D ) $.
ntp4vc-poke-spec-syntax
  $a wff ( NTP4VCPokeSpec A B C D E F ) $.

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

ntp4vc-max-value-definition $a |- (
  NTP4VCMaxValue A
) = (
  ( 2 ^ A ) mod ( 2 ^ ; 6 4 )
) $.

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.

  ntp4vc-read-spec-definition $a |- (
    NTP4VCReadSpec A B C D
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
  $d i A $.  $d i B $.  $d i C $.
  $d i D $.  $d i E $.  $d i F $.

  ntp4vc-poke-spec-definition $a |- (
    NTP4VCPokeSpec A B C D E F
  ) <-> (
    (
      ( -u 2 ) <_ F
      /\
      F <_ 0
    )
    /\
    (
      (
        F = ( -u 1 )
        <->
        (
          ( 8 x. ( # ` E ) )
          <
          ( B + A )
        )
      )
      /\
      (
        (
          F = ( -u 2 )
          <->
          (
            ( NTP4VCMaxValue A ) <_ D
            /\
            (
              ( B + A )
              <_
              ( 8 x. ( # ` E ) )
            )
          )
        )
        /\
        (
          (
            F = 0
            <->
            (
              D < ( NTP4VCMaxValue A )
              /\
              (
                ( B + A )
                <_
                ( 8 x. ( # ` E ) )
              )
            )
          )
          /\
          (
            F = 0
            ->
            (
              A. i e. ZZ
                (
                  (
                    0 <_ i
                    /\
                    i < B
                  )
                  ->
                  (
                    NTP4VCNth8Stream C i
                  )
                  =
                  (
                    NTP4VCNth8Stream E i
                  )
                )
              /\
              (
                A. i e. ZZ
                  (
                    (
                      B <_ i
                      /\
                      i < ( B + A )
                    )
                    ->
                    (
                      NTP4VCNth8Stream E i
                    )
                    =
                    (
                      NTP4VCBit
                        D
                        ( ( ( A - i ) - 1 ) + B )
                        ; 6 4
                    )
                  )
                /\
                A. i e. ZZ
                  (
                    (
                      ( B + A ) <_ i
                      /\
                      i < ( 8 x. ( # ` E ) )
                    )
                    ->
                    (
                      NTP4VCNth8Stream E i
                    )
                    =
                    (
                      NTP4VCNth8Stream C i
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
  $d e A $.  $d e B $.  $d e C $.  $d e D $.
  $d r A $.  $d r B $.  $d r C $.  $d r D $.  $d r e $.
  $d v A $.  $d v B $.  $d v C $.  $d v D $.  $d v e $.  $d v r $.

  $( Source parameters: A=len, B=start, C=value, and D=addr. $)

  ntp4vc-len-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-start-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-value-word64 $e |- C e. NTP4VCWord64 $.
  ntp4vc-addr-byte-stream $e |- D e. Word NTP4VCByte $.

  ntp4vc-stream-bit-length-in-range
    $e |- ( 8 x. ( # ` D ) ) < ; 4 2 9 4 9 6 7 2 9 6 $.
  ntp4vc-len-nonnegative $e |- 0 <_ A $.
  ntp4vc-len-less-than-64 $e |- A < ; 6 4 $.
  ntp4vc-start-plus-len-in-stream
    $e |- ( B + A ) <_ ( 8 x. ( # ` D ) ) $.
  ntp4vc-value-below-maximum
    $e |- C < ( NTP4VCMaxValue A ) $.

  ntp4vc-pearl-bitwalker-pokethenpeek-vc $a |- (
    A < ; 6 4
    /\
    (
      ( B + A ) < ; 4 2 9 4 9 6 7 2 9 6
      /\
      (
        ( 8 x. ( # ` D ) ) < ; 4 2 9 4 9 6 7 2 9 6
        /\
        A. e e. Word NTP4VCByte
          (
            ( # ` e ) = ( # ` D )
            ->
            A. r e. ZZ
              (
                ( NTP4VCPokeSpec A B D C e r )
                ->
                (
                  (
                    A <_ ; 6 4
                    /\
                    (
                      ( B + A ) < ; 4 2 9 4 9 6 7 2 9 6
                      /\
                      (
                        ( 8 x. ( # ` e ) )
                        <
                        ; 4 2 9 4 9 6 7 2 9 6
                      )
                    )
                  )
                  /\
                  A. v e. NTP4VCWord64
                    (
                      ( NTP4VCReadSpec A B e v )
                      ->
                      v = C
                    )
                )
              )
          )
      )
    )
  ) $.
$}
