$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitcount_AsciiCode_asciiqtvc: the ASCII-code verification condition
  sets the high bit of a 32-bit word from its population count and requires
  preservation of the low 31 bits together with an even resulting population
  count. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A 32-bit word is represented exactly by its unsigned integer value in
  0 through 2^32-1. NTP4VCBit is binary digit extraction,
  NTP4VCCount is the sum of all 32 digits, NTP4VCShiftL32 is fixed-width
  left shift modulo 2^32, and NTP4VCOr32 is bitwise disjunction reconstructed
  from the 32 binary digits. NTP4VCEqSub32 compares the requested bit slice;
  at offset zero and width 31 it is exactly equality of the low 31 bits.
  NTP4VCValidAscii is evenness of the population count.

  The source Boolean hypothesis that bit 31 of b is not true is equivalently
  digit 31 = 0. Unsigned conversion is the identity on this exact word
  carrier. Source let bindings are expanded by substitution, while the
  duplicated shift equality and both disjuncts of the bounds obligation
  remain explicit. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCWord32 NTP4VCBit NTP4VCCount NTP4VCShiftL32
  NTP4VCOr32 NTP4VCEqSub32 NTP4VCValidAscii NTP4VCUlt32
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-bit-syntax $a class ( NTP4VCBit A B ) $.
ntp4vc-count-syntax $a class ( NTP4VCCount A ) $.
ntp4vc-shift-left-syntax $a class ( NTP4VCShiftL32 A B ) $.
ntp4vc-or-syntax $a class ( NTP4VCOr32 A B ) $.
ntp4vc-eq-sub-syntax $a wff ( NTP4VCEqSub32 A B C D ) $.
ntp4vc-valid-ascii-syntax $a wff ( NTP4VCValidAscii A ) $.
ntp4vc-ult-syntax $a wff ( NTP4VCUlt32 A B ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-bit-definition $a |- ( NTP4VCBit A B ) =
  ( ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2 ) $.

${
  $d k A $.

  ntp4vc-count-definition $a |- ( NTP4VCCount A ) =
    sum_ k e. ( 0 ... ; 3 1 ) ( NTP4VCBit A k ) $.
$}

ntp4vc-shift-left-definition $a |- ( NTP4VCShiftL32 A B ) =
  ( ( A x. ( 2 ^ B ) ) mod ( 2 ^ ; 3 2 ) ) $.

${
  $d k A $.  $d k B $.

  ntp4vc-or-definition $a |- ( NTP4VCOr32 A B ) =
    sum_ k e. ( 0 ... ; 3 1 )
      if (
        (
          ( ( NTP4VCBit A k ) = 1 )
          \/
          ( ( NTP4VCBit B k ) = 1 )
        ) ,
        ( 2 ^ k ) ,
        0
      ) $.
$}

ntp4vc-eq-sub-definition $a |- (
  ( NTP4VCEqSub32 A B C D )
  <->
  (
    ( ( |_ ` ( A / ( 2 ^ C ) ) ) mod ( 2 ^ D ) )
    =
    ( ( |_ ` ( B / ( 2 ^ C ) ) ) mod ( 2 ^ D ) )
  )
) $.

ntp4vc-valid-ascii-definition $a |- (
  ( NTP4VCValidAscii A )
  <->
  ( ( ( NTP4VCCount A ) mod 2 ) = 0 )
) $.

ntp4vc-ult-definition $a |- (
  ( NTP4VCUlt32 A B )
  <->
  A < B
) $.

${
  $( Source theorem parameters: A=b and B=c. $)

  ntp4vc-b-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-c-word32 $e |- B e. NTP4VCWord32 $.

  ntp4vc-b-high-bit-clear $e |- ( NTP4VCBit A ; 3 1 ) = 0 $.
  ntp4vc-c-is-count $e |- B = ( NTP4VCCount A ) $.

  ntp4vc-pearl-bitcount-ascii-code-vc $a |- (
    (
      ( NTP4VCUlt32 ; 3 1 ; 3 2 )
      \/
      ; 3 1 < ; 3 2
    )
    /\
    (
      ( NTP4VCShiftL32 B ; 3 1 )
      =
      ( NTP4VCShiftL32 B ; 3 1 )
      ->
      (
        (
          NTP4VCEqSub32
            ( NTP4VCOr32 A ( NTP4VCShiftL32 B ; 3 1 ) )
            A
            0
            ; 3 1
        )
        /\
        (
          NTP4VCValidAscii
            ( NTP4VCOr32 A ( NTP4VCShiftL32 B ; 3 1 ) )
        )
      )
    )
  ) $.
$}
