$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/bitcount_Hamming_hammingDqtvc: the 32-bit Hamming-distance
  verification condition identifies the population count of the bitwise XOR
  of two words with the number of bit positions at which they differ.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned value from zero
  through 2^32-1. NTP4VCBit32 is binary digit extraction. NTP4VCXor32
  reconstructs the fixed-width bitwise exclusive-or from all 32 digits,
  NTP4VCCount32 is the sum of those 32 digits, and NTP4VCHammingD32 is the
  sum of the 32 indicators that the corresponding input digits differ.

  Thus NTP4VCCount32 applied to NTP4VCXor32 is definitionally the source
  count_logic applied to a XOR b after expanding nth_closure_def, while
  NTP4VCHammingD32 is definitionally the source hammingD_logic after expanding
  nth_diff_closure_def. Unsigned conversion is the identity on the exact word
  carrier. The three arbitrary parameters retain the complete 32-bit domain,
  and the scoped equality hypothesis and asserted equality reproduce the
  source premise and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCBit32 NTP4VCXor32
  NTP4VCCount32 NTP4VCHammingD32
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-bit32-syntax $a class ( NTP4VCBit32 A B ) $.
ntp4vc-xor32-syntax $a class ( NTP4VCXor32 A B ) $.
ntp4vc-count32-syntax $a class ( NTP4VCCount32 A ) $.
ntp4vc-hamming-d32-syntax $a class ( NTP4VCHammingD32 A B ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-bit32-definition $a |- ( NTP4VCBit32 A B ) =
  ( ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2 ) $.

${
  $d k A $.  $d k B $.

  ntp4vc-xor32-definition $a |- ( NTP4VCXor32 A B ) =
    sum_ k e. ( 0 ... ; 3 1 )
      if (
        ( NTP4VCBit32 A k ) =/= ( NTP4VCBit32 B k ) ,
        ( 2 ^ k ) ,
        0
      ) $.
$}

${
  $d k A $.

  ntp4vc-count32-definition $a |- ( NTP4VCCount32 A ) =
    sum_ k e. ( 0 ... ; 3 1 ) ( NTP4VCBit32 A k ) $.
$}

${
  $d k A $.  $d k B $.

  ntp4vc-hamming-d32-definition $a |- ( NTP4VCHammingD32 A B ) =
    sum_ k e. ( 0 ... ; 3 1 )
      if (
        ( NTP4VCBit32 A k ) =/= ( NTP4VCBit32 B k ) ,
        1 ,
        0
      ) $.
$}

${
  $( Source theorem parameters: A=result, B=a, and C=b. $)

  ntp4vc-result-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-a-word32 $e |- B e. NTP4VCWord32 $.
  ntp4vc-b-word32 $e |- C e. NTP4VCWord32 $.

  ntp4vc-result-is-xor-count $e |- A =
    ( NTP4VCCount32 ( NTP4VCXor32 B C ) ) $.

  ntp4vc-pearl-bitcount-hamming-d-vc $a |- A =
    ( NTP4VCHammingD32 B C ) $.
$}
