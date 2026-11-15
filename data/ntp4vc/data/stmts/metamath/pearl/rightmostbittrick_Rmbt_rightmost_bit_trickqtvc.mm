$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/rightmostbittrick_Rmbt_rightmost_bit_trickqtvc: the 64-bit
  rightmost-set-bit verification condition states that, at the first set-bit
  position of a nonzero word, x conjoined with its fixed-width negation has
  that bit set and every lower and higher bit clear. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A source 64-bit word is represented exactly by its unsigned integer value
  from zero through 2^64-1. NTP4VCBit64 is binary digit extraction,
  NTP4VCNeg64 is fixed-width two's-complement negation, and NTP4VCAnd64
  reconstructs bitwise conjunction from all 64 binary digits.

  NTP4VCEqSub64 A B C D states equality of the D consecutive binary digits
  of A and B beginning at offset C. Thus its word-valued offset and length
  arguments in eq_sub_bv, and its integer-valued arguments in eq_sub, have
  the same exact unsigned values in this encoding. NTP4VCRightmost64 is the
  source let-bound expression x AND (-x).

  The quantified position ranges over the complete 64-bit carrier; the
  source antecedent retains its unsigned bound below 64. Every lower-prefix,
  selected-bit, and upper-suffix condition is explicit. The generated source
  VC repeats its x-not-zero hypothesis as the first conclusion conjunct, so
  that repetition is retained verbatim rather than simplified away. The
  final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p declaration.
$)

$c
  NTP4VCWord64 NTP4VCBit64 NTP4VCNeg64 NTP4VCAnd64
  NTP4VCEqSub64 NTP4VCRightmost64
$.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-bit64-syntax $a class ( NTP4VCBit64 A B ) $.
ntp4vc-neg64-syntax $a class ( NTP4VCNeg64 A ) $.
ntp4vc-and64-syntax $a class ( NTP4VCAnd64 A B ) $.
ntp4vc-eq-sub64-syntax
  $a wff ( NTP4VCEqSub64 A B C D ) $.
ntp4vc-rightmost64-syntax
  $a class ( NTP4VCRightmost64 A ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-bit64-definition $a |- (
  NTP4VCBit64 A B
) = (
  ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
) $.

ntp4vc-neg64-definition $a |- (
  NTP4VCNeg64 A
) = (
  ( -u A ) mod ( 2 ^ ; 6 4 )
) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and64-definition $a |- (
    NTP4VCAnd64 A B
  ) = sum_ k e. ( 0 ... ; 6 3 )
    if (
      (
        ( ( NTP4VCBit64 A k ) = 1 )
        /\
        ( ( NTP4VCBit64 B k ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

ntp4vc-eq-sub64-definition $a |- (
  NTP4VCEqSub64 A B C D
) <-> (
  (
    ( |_ ` ( A / ( 2 ^ C ) ) )
    mod
    ( 2 ^ D )
  )
  =
  (
    ( |_ ` ( B / ( 2 ^ C ) ) )
    mod
    ( 2 ^ D )
  )
) $.

ntp4vc-rightmost64-definition $a |- (
  NTP4VCRightmost64 A
) = (
  NTP4VCAnd64 A ( NTP4VCNeg64 A )
) $.

${
  $d i A $.

  $( Source parameter A=x and assumption fact0. $)
  ntp4vc-x-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-x-nonzero $e |- A =/= 0 $.

  ntp4vc-pearl-rightmostbittrick-rightmost-bit-trick-vc $a |- (
    A =/= 0
    /\
    A. i e. NTP4VCWord64
      (
        (
          i < ; 6 4
          /\
          (
            ( NTP4VCEqSub64 A 0 0 i )
            /\
            ( NTP4VCBit64 A i ) = 1
          )
        )
        ->
        (
          (
            0 <_ i
            /\
            i < ; 6 4
          )
          /\
          (
            ( NTP4VCEqSub64 A 0 0 i )
            /\
            (
              ( NTP4VCBit64 A i ) = 1
              /\
              (
                (
                  NTP4VCEqSub64
                    ( NTP4VCRightmost64 A )
                    0
                    0
                    i
                )
                /\
                (
                  (
                    NTP4VCEqSub64
                      ( NTP4VCRightmost64 A )
                      0
                      ( i + 1 )
                      ( ; 6 3 - i )
                  )
                  /\
                  (
                    NTP4VCBit64
                      ( NTP4VCRightmost64 A )
                      i
                  ) = 1
                )
              )
            )
          )
        )
      )
  ) $.
$}
