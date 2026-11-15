$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/div_Div_invert_limbqtvc: the verification condition
  for computing the reciprocal approximation of a normalized 64-bit
  unsigned divisor, including the intermediate subtraction bound and the
  final reciprocal identity. This file contains no proof.

  Source 64-bit words are represented exactly by the integer interval
  [0, 2^64 - 1], in bijection with their unsigned values. The normalization
  hypothesis makes every divisor positive, so Metamath's floor quotient
  agrees with Why3's Euclidean division. The source let-binding for the
  maximum 64-bit word is inlined, while both word-typed universal
  quantifiers and their implication scopes are preserved exactly.
$)

$[ lib/set.mm $]

$c NTP4VCWord64 NTP4VCUInt64InBounds NTP4VCReciprocal $.

ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-uint64-in-bounds-syntax
  $a wff ( NTP4VCUInt64InBounds A ) $.
ntp4vc-reciprocal-syntax
  $a wff ( NTP4VCReciprocal A B ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-uint64-in-bounds-definition $a |- (
  NTP4VCUInt64InBounds A
) <-> (
  A e. NTP4VCWord64
) $.

ntp4vc-reciprocal-definition $a |- (
  NTP4VCReciprocal A B
) <-> (
  A =
  (
    ( |_ `
      (
        (
          (
            ( 2 ^ ; 6 4 )
            x.
            ( 2 ^ ; 6 4 )
          )
          -
          1
        )
        /
        B
      )
    )
    -
    ( 2 ^ ; 6 4 )
  )
) $.

${
  $d q A $.
  $d v A $.
  $d q v $.

  ntp4vc-d-word64 $e |- A e. NTP4VCWord64 $.

  ntp4vc-fact0 $e |- (
    ( |_ ` ( ( 2 ^ ; 6 4 ) / 2 ) )
    <_
    A
  ) $.

  ntp4vc-pearl-multiprecision-div-invert-limb-vc $a |- (
    (
      NTP4VCUInt64InBounds
      (
        ( ( 2 ^ ; 6 4 ) - 1 )
        -
        A
      )
    )
    /\
    A. q e. NTP4VCWord64
      (
        q =
        (
          ( ( 2 ^ ; 6 4 ) - 1 )
          -
          A
        )
        ->
        (
          q < A
          /\
          A. v e. NTP4VCWord64
            (
              v =
              (
                |_ `
                (
                  (
                    ( ( 2 ^ ; 6 4 ) - 1 )
                    +
                    ( ( 2 ^ ; 6 4 ) x. q )
                  )
                  /
                  A
                )
              )
              ->
              ( NTP4VCReciprocal v A )
            )
        )
      )
  ) $.
$}
