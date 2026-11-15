$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_64bit_bvqtvc: the 64-bit poke verification
  condition sets or clears the bit at position 63 minus a bounded 32-bit
  index, preserves every other bit, and relates word-indexed and
  integer-indexed bit specifications. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An n-bit word is represented exactly by its unsigned integer value in
  0 through 2^n-1. The source Boolean is represented by SetMM's exact
  two-element carrier 2, with false=0 and true=1. NTP4VCBit is totalized
  fixed-width extraction: its index is converted as Int.toNat and an
  out-of-range access returns false. Thus quantification over NTP4VCWord32
  retains all 2^32 source indices, including those outside a 64-bit word.

  NTP4VCSub32 and NTP4VCShiftL64 are fixed-width operations modulo their
  word sizes. NTP4VCAnd64 and NTP4VCOr64 reconstruct the corresponding
  bitwise operations from all 64 binary digits, and NTP4VCNot64 is the
  64-bit complement. Zero extension from 32 to 64 bits is the identity on
  the exact unsigned carrier.

  NTP4VCUpdate64 renders the source Boolean match as an exhaustive guarded
  disjunction. The match whose two branches are True is retained as the
  equivalent exhaustive Boolean disjunction. NTP4VCWordPost and
  NTP4VCIntPost reproduce the word-indexed and integer-indexed bit
  specifications. Expanding NTP4VCPoke64VC recovers the source conjunctions,
  implications, quantifiers, bounds, and let-bound values exactly.

  The scoped essential hypotheses are bidirectionally equivalent to the
  source theorem's three typed parameters and its unsigned-bound assumption.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCWord64
  NTP4VCToNat NTP4VCBit NTP4VCSub32 NTP4VCShiftL64
  NTP4VCAnd64 NTP4VCOr64 NTP4VCNot64
  NTP4VCUpdate64 NTP4VCWordPost NTP4VCIntPost NTP4VCPoke64VC
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-bit-syntax $a class ( NTP4VCBit A B C ) $.
ntp4vc-sub32-syntax $a class ( NTP4VCSub32 A B ) $.
ntp4vc-shiftl64-syntax $a class ( NTP4VCShiftL64 A B ) $.
ntp4vc-and64-syntax $a class ( NTP4VCAnd64 A B ) $.
ntp4vc-or64-syntax $a class ( NTP4VCOr64 A B ) $.
ntp4vc-not64-syntax $a class ( NTP4VCNot64 A ) $.
ntp4vc-update64-syntax
  $a wff ( NTP4VCUpdate64 A B C D ) $.
ntp4vc-word-post-syntax
  $a wff ( NTP4VCWordPost A B C D ) $.
ntp4vc-int-post-syntax
  $a wff ( NTP4VCIntPost A B C D ) $.
ntp4vc-poke64-vc-syntax
  $a wff ( NTP4VCPoke64VC A B C ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

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

ntp4vc-sub32-definition $a |- (
  NTP4VCSub32 A B
) = (
  ( A - B ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-shiftl64-definition $a |- (
  NTP4VCShiftL64 A B
) = (
  ( A x. ( 2 ^ B ) ) mod ( 2 ^ ; 6 4 )
) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and64-definition $a |- (
    NTP4VCAnd64 A B
  ) = sum_ k e. ( 0 ... ; 6 3 )
    if (
      (
        ( ( NTP4VCBit A k ; 6 4 ) = 1 )
        /\
        ( ( NTP4VCBit B k ; 6 4 ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

${
  $d k A $.  $d k B $.

  ntp4vc-or64-definition $a |- (
    NTP4VCOr64 A B
  ) = sum_ k e. ( 0 ... ; 6 3 )
    if (
      (
        ( ( NTP4VCBit A k ; 6 4 ) = 1 )
        \/
        ( ( NTP4VCBit B k ; 6 4 ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

ntp4vc-not64-definition $a |- (
  NTP4VCNot64 A
) = (
  ( ( 2 ^ ; 6 4 ) - 1 ) - A
) $.

ntp4vc-update64-definition $a |- (
  NTP4VCUpdate64 A B C D
) <-> (
  (
    B = 1
    /\
    A = ( NTP4VCOr64 C D )
  )
  \/
  (
    B = 0
    /\
    A = ( NTP4VCAnd64 C ( NTP4VCNot64 D ) )
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
          i =/= ( NTP4VCSub32 ; 6 3 D )
          ->
          (
            NTP4VCBit A i ; 6 4
          )
          =
          (
            NTP4VCBit C i ; 6 4
          )
        )
    )
    /\
    B = (
      NTP4VCBit
        A
        ( NTP4VCSub32 ; 6 3 D )
        ; 6 4
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
              i < ; 6 4
            )
            /\
            i =/= ( ; 6 3 - D )
          )
          ->
          (
            NTP4VCBit A i ; 6 4
          )
          =
          (
            NTP4VCBit C i ; 6 4
          )
        )
    )
    /\
    B = (
      NTP4VCBit A ( ; 6 3 - D ) ; 6 4
    )
  ) $.
$}

${
  $d r A $.  $d r B $.  $d r C $.

  ntp4vc-poke64-vc-definition $a |- (
    NTP4VCPoke64VC A B C
  ) <-> (
    (
      A <_ ; 6 3
      \/
      A <_ ; 6 3
    )
    /\
    (
      (
        (
          NTP4VCSub32 ; 6 3 A
        )
        =
        ( ; 6 3 - A )
        ->
        (
          (
            B = 1
            \/
            B = 0
          )
          /\
          A. r e. NTP4VCWord64
            (
              (
                NTP4VCUpdate64
                  r
                  B
                  C
                  (
                    NTP4VCShiftL64
                      1
                      ( NTP4VCSub32 ; 6 3 A )
                  )
              )
              ->
              ( NTP4VCWordPost r B C A )
            )
        )
      )
      /\
      A. r e. NTP4VCWord64
        (
          ( NTP4VCWordPost r B C A )
          ->
          ( NTP4VCIntPost r B C A )
        )
    )
  ) $.
$}

${
  $( Source theorem parameters: A=left1, B=flag, and C=value. $)

  ntp4vc-left1-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-flag-boolean $e |- B e. { 0 , 1 } $.
  ntp4vc-value-word64 $e |- C e. NTP4VCWord64 $.

  ntp4vc-left1-less-than-64 $e |- A < ; 6 4 $.

  ntp4vc-pearl-bitwalker-poke-64bit-vc $a |- (
    NTP4VCPoke64VC A B C
  ) $.
$}
