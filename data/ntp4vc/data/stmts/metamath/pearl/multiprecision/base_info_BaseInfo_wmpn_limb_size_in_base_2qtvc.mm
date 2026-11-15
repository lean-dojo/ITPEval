$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc:
  the multiprecision limb-size verification condition derives a value from
  1 through 64 whose adjacent powers of two bracket a positive 64-bit limb.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32- or 64-bit word is represented exactly by its complete unsigned
  integer carrier. NTP4VCSigned32 is the standard two's-complement conversion
  of a 32-bit word. NTP4VCToNat renders the exported Int.toNat exponent
  conversion, and NTP4VCPow2 therefore agrees with the source power terms on
  every integer while retaining their exact values on the nonnegative
  exponents required by the verification condition.

  NTP4VCUInt64InBounds is the Why3 unsigned-64 conversion obligation
  0 <= x < 2^64. NTP4VCAntecedent is the leading-zero characterization of
  o1. NTP4VCShiftObligation preserves the universally quantified shift and r
  witnesses, their equality guards, and the final adjacent-power bounds.
  NTP4VCLimbSizeVC expands to the complete source conjunction and implication
  structure. The scoped essential hypotheses are exactly the typed parameter
  u and its positivity assumption. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCSigned32
  NTP4VCToNat NTP4VCPow2 NTP4VCUInt64InBounds
  NTP4VCAntecedent NTP4VCShiftObligation NTP4VCLimbSizeVC
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-signed32-syntax $a class ( NTP4VCSigned32 A ) $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-pow2-syntax $a class ( NTP4VCPow2 A ) $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-antecedent-syntax
  $a wff ( NTP4VCAntecedent A B ) $.
ntp4vc-shift-obligation-syntax
  $a wff ( NTP4VCShiftObligation A B C ) $.
ntp4vc-limb-size-vc-syntax
  $a wff ( NTP4VCLimbSizeVC A ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-signed32-definition $a |- ( NTP4VCSigned32 A ) =
  if (
    A < ( 2 ^ ; 3 1 ) ,
    A ,
    ( A - ( 2 ^ ; 3 2 ) )
  ) $.

ntp4vc-to-nat-definition $a |- ( NTP4VCToNat A ) =
  if (
    0 <_ A ,
    A ,
    0
  ) $.

ntp4vc-pow2-definition $a |- ( NTP4VCPow2 A ) =
  ( 2 ^ ( NTP4VCToNat A ) ) $.

ntp4vc-uint64-in-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. ZZ
  /\
  (
    0 <_ A
    /\
    A < ( 2 ^ ; 6 4 )
  )
) $.

ntp4vc-antecedent-definition $a |- (
  NTP4VCAntecedent A B
) <-> (
  (
    (
      ( NTP4VCPow2 ( NTP4VCSigned32 B ) )
      x. A
    ) <_ ( ( 2 ^ ; 6 4 ) - 1 )
  )
  /\
  (
    ( ( 2 ^ ; 6 4 ) - 1 ) <
      (
        2 x.
        (
          ( NTP4VCPow2 ( NTP4VCSigned32 B ) )
          x. A
        )
      )
    /\
    (
      0 <_ ( NTP4VCSigned32 B )
      /\
      ( NTP4VCSigned32 B ) < ; 6 4
    )
  )
) $.

${
  $d r A $.  $d r B $.  $d r C $.

  ntp4vc-shift-obligation-definition $a |- (
    NTP4VCShiftObligation A B C
  ) <-> (
    C = ( NTP4VCSigned32 B )
    ->
    (
      ( NTP4VCUInt64InBounds ( ; 6 4 - C ) )
      /\
      A. r e. NTP4VCWord64
        (
          r = ( ; 6 4 - C )
          ->
          (
            (
              1 <_ r
              /\
              r <_ ; 6 4
            )
            /\
            (
              ( NTP4VCPow2 ( r - 1 ) ) <_ A
              /\
              A < ( NTP4VCPow2 r )
            )
          )
        )
    )
  ) $.
$}

${
  $d o A $.  $d s A $.  $d o s $.

  ntp4vc-limb-size-vc-definition $a |- (
    NTP4VCLimbSizeVC A
  ) <-> (
    0 < A
    /\
    A. o e. NTP4VCWord32
      (
        ( NTP4VCAntecedent A o )
        ->
        (
          0 <_ ( NTP4VCSigned32 o )
          /\
          A. s e. NTP4VCWord64
            ( NTP4VCShiftObligation A o s )
        )
      )
  ) $.
$}

${
  $( Source theorem parameter A=u and assumption fact0. $)

  ntp4vc-u-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-u-positive $e |- 0 < A $.

  ntp4vc-pearl-multiprecision-base-info-limb-size-in-base-2-vc
    $a |- ( NTP4VCLimbSizeVC A ) $.
$}
