$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_8bitqtvc: the 8-bit poke verification
  condition sets or clears the bit at position 7 minus a bounded 32-bit
  index, preserves every other bit, and relates word-indexed and
  integer-indexed bit specifications. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An n-bit word is represented exactly by its unsigned integer value in
  0 through 2^n-1. The source Boolean is represented by SetMM's exact
  two-element carrier 2, with false=0 and true=1. NTP4VCBit is totalized
  fixed-width extraction: its index is converted as Int.toNat and an
  out-of-range access returns false.

  NTP4VCTrunc8, NTP4VCSub8, NTP4VCSub32, and NTP4VCShiftL8 reproduce the
  source fixed-width operations modulo their word sizes. NTP4VCAnd8 and
  NTP4VCOr8 reconstruct the corresponding bitwise operations from all eight
  binary digits, and NTP4VCNot8 is the 8-bit complement.

  NTP4VCUpdate8 renders the source Boolean match as an exhaustive guarded
  disjunction. The match whose two branches are True is retained as the
  equivalent exhaustive Boolean disjunction. NTP4VCWordPost and
  NTP4VCIntPost reproduce the word-indexed and integer-indexed bit
  specifications, including the 32-bit bound and fixed-width index
  conversion. Expanding NTP4VCPoke8VC recovers the source conjunctions,
  implications, quantifiers, bounds, and let-bound values exactly.

  The scoped essential hypotheses are bidirectionally equivalent to the
  source theorem's three typed parameters and its unsigned-bound assumption.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCWord8 NTP4VCWord32
  NTP4VCToNat NTP4VCBit NTP4VCTrunc8
  NTP4VCSub8 NTP4VCSub32 NTP4VCShiftL8
  NTP4VCAnd8 NTP4VCOr8 NTP4VCNot8
  NTP4VCUpdate8 NTP4VCWordPost NTP4VCIntPost NTP4VCPoke8VC
$.

ntp4vc-word8-syntax $a class NTP4VCWord8 $.
ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-bit-syntax $a class ( NTP4VCBit A B C ) $.
ntp4vc-trunc8-syntax $a class ( NTP4VCTrunc8 A ) $.
ntp4vc-sub8-syntax $a class ( NTP4VCSub8 A B ) $.
ntp4vc-sub32-syntax $a class ( NTP4VCSub32 A B ) $.
ntp4vc-shiftl8-syntax $a class ( NTP4VCShiftL8 A B ) $.
ntp4vc-and8-syntax $a class ( NTP4VCAnd8 A B ) $.
ntp4vc-or8-syntax $a class ( NTP4VCOr8 A B ) $.
ntp4vc-not8-syntax $a class ( NTP4VCNot8 A ) $.
ntp4vc-update8-syntax
  $a wff ( NTP4VCUpdate8 A B C D ) $.
ntp4vc-word-post-syntax
  $a wff ( NTP4VCWordPost A B C D ) $.
ntp4vc-int-post-syntax
  $a wff ( NTP4VCIntPost A B C D ) $.
ntp4vc-poke8-vc-syntax
  $a wff ( NTP4VCPoke8VC A B C ) $.

ntp4vc-word8-definition $a |- NTP4VCWord8 =
  ( 0 ... ( ( 2 ^ 8 ) - 1 ) ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

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

ntp4vc-trunc8-definition $a |- (
  NTP4VCTrunc8 A
) = (
  A mod ( 2 ^ 8 )
) $.

ntp4vc-sub8-definition $a |- (
  NTP4VCSub8 A B
) = (
  ( A - B ) mod ( 2 ^ 8 )
) $.

ntp4vc-sub32-definition $a |- (
  NTP4VCSub32 A B
) = (
  ( A - B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-shiftl8-definition $a |- (
  NTP4VCShiftL8 A B
) = (
  ( A x. ( 2 ^ B ) ) mod ( 2 ^ 8 )
) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and8-definition $a |- (
    NTP4VCAnd8 A B
  ) = sum_ k e. ( 0 ... 7 )
    if (
      (
        ( ( NTP4VCBit A k 8 ) = 1 )
        /\
        ( ( NTP4VCBit B k 8 ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

${
  $d k A $.  $d k B $.

  ntp4vc-or8-definition $a |- (
    NTP4VCOr8 A B
  ) = sum_ k e. ( 0 ... 7 )
    if (
      (
        ( ( NTP4VCBit A k 8 ) = 1 )
        \/
        ( ( NTP4VCBit B k 8 ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

ntp4vc-not8-definition $a |- (
  NTP4VCNot8 A
) = (
  ( ( 2 ^ 8 ) - 1 ) - A
) $.

ntp4vc-update8-definition $a |- (
  NTP4VCUpdate8 A B C D
) <-> (
  (
    B = 1
    /\
    A = ( NTP4VCOr8 C D )
  )
  \/
  (
    B = 0
    /\
    A = ( NTP4VCAnd8 C ( NTP4VCNot8 D ) )
  )
) $.

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.

  ntp4vc-word-post-definition $a |- (
    NTP4VCWordPost A B C D
  ) <-> (
    (
      A. i e. NTP4VCWord32
        (
          (
            i < 8
            /\
            i =/= ( NTP4VCSub32 7 D )
          )
          ->
          (
            NTP4VCBit
              A
              ( NTP4VCTrunc8 i )
              8
          )
          =
          (
            NTP4VCBit
              C
              ( NTP4VCTrunc8 i )
              8
          )
        )
    )
    /\
    B = (
      NTP4VCBit
        A
        ( NTP4VCSub8 7 ( NTP4VCTrunc8 D ) )
        8
    )
  ) $.
$}

${
  $d i A $.  $d i B $.  $d i C $.  $d i D $.

  ntp4vc-int-post-definition $a |- (
    NTP4VCIntPost A B C D
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < 8
            )
            /\
            i =/= ( 7 - D )
          )
          ->
          (
            NTP4VCBit A i 8
          )
          =
          (
            NTP4VCBit C i 8
          )
        )
    )
    /\
    B = (
      NTP4VCBit A ( 7 - D ) 8
    )
  ) $.
$}

${
  $d r A $.  $d r B $.  $d r C $.

  ntp4vc-poke8-vc-definition $a |- (
    NTP4VCPoke8VC A B C
  ) <-> (
    (
      ( NTP4VCTrunc8 A ) <_ 7
      \/
      ( NTP4VCTrunc8 A ) <_ 7
    )
    /\
    (
      (
        (
          NTP4VCSub8 7 ( NTP4VCTrunc8 A )
        )
        =
        ( 7 - ( NTP4VCTrunc8 A ) )
        ->
        (
          (
            B = 1
            \/
            B = 0
          )
          /\
          A. r e. NTP4VCWord8
            (
              (
                NTP4VCUpdate8
                  r
                  B
                  C
                  (
                    NTP4VCShiftL8
                      1
                      (
                        NTP4VCSub8
                          7
                          ( NTP4VCTrunc8 A )
                      )
                  )
              )
              ->
              ( NTP4VCWordPost r B C A )
            )
        )
      )
      /\
      A. r e. NTP4VCWord8
        (
          ( NTP4VCWordPost r B C A )
          ->
          ( NTP4VCIntPost r B C A )
        )
    )
  ) $.
$}

${
  $( Source theorem parameters: A=left1, B=flag, and C=byte. $)

  ntp4vc-left1-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-flag-boolean $e |- B e. { 0 , 1 } $.
  ntp4vc-byte-word8 $e |- C e. NTP4VCWord8 $.

  ntp4vc-left1-less-than-8 $e |- A < 8 $.

  ntp4vc-pearl-bitwalker-poke-8bit-vc $a |- (
    NTP4VCPoke8VC A B C
  ) $.
$}
