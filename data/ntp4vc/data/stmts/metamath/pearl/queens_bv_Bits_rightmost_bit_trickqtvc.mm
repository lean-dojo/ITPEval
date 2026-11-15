$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/queens_bv_Bits_rightmost_bit_trickqtvc: the 32-bit rightmost-set-bit
  verification condition states that a word conjoined with its fixed-width
  negation represents exactly the singleton containing its least set-bit
  position. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned value from zero
  through 2^32-1. NTP4VCBit32 is binary digit extraction on the guarded
  indices zero through 31. NTP4VCNeg32 is fixed-width two's-complement
  negation, and NTP4VCAnd32 reconstructs bitwise conjunction from all 32
  binary digits.

  NTP4VCFSet is the full carrier of finite integer sets, and NTP4VCMinElt
  uses restricted definite description for the unique least member of a
  finite nonempty integer set. The source invokes its minimum operation only
  under the explicit nonempty premise retained below.

  B is an arbitrary nonempty source state carrier; C and D are respectively
  its 32-bit-word and finite-integer-set accessors. NTP4VCStateInvariant and
  NTP4VCStateInjective reproduce the source record invariant and extensional
  injectivity law on every state.

  Expanding NTP4VCRightmostVC substitutes the source let-bound word and
  singleton set definitionally. It retains the full integer bit-position
  quantifier and the universally quantified result-state postcondition.
  Every auxiliary $a below is syntax or an explicit faithful definition
  required by the target. The final $a is Metamath's native unproved statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCFSet NTP4VCBit32 NTP4VCNeg32 NTP4VCAnd32
  NTP4VCMinElt NTP4VCRightmost32
  NTP4VCStateInvariant NTP4VCStateInjective NTP4VCRightmostVC
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-fset-syntax $a class NTP4VCFSet $.
ntp4vc-bit32-syntax $a class ( NTP4VCBit32 A B ) $.
ntp4vc-neg32-syntax $a class ( NTP4VCNeg32 A ) $.
ntp4vc-and32-syntax $a class ( NTP4VCAnd32 A B ) $.
ntp4vc-min-elt-syntax $a class ( NTP4VCMinElt A ) $.
ntp4vc-rightmost32-syntax $a class ( NTP4VCRightmost32 A ) $.
ntp4vc-state-invariant-syntax
  $a wff ( NTP4VCStateInvariant A B C ) $.
ntp4vc-state-injective-syntax
  $a wff ( NTP4VCStateInjective A B C ) $.
ntp4vc-rightmost-vc-syntax
  $a wff ( NTP4VCRightmostVC A B C D ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

${
  ntp4vc-fset-definition $a |- NTP4VCFSet = {
    x e. Fin | x C_ ZZ
  } $.
$}

ntp4vc-bit32-definition $a |- (
  NTP4VCBit32 A B
) = (
  ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
) $.

ntp4vc-neg32-definition $a |- (
  NTP4VCNeg32 A
) = (
  ( -u A ) mod ( 2 ^ ; 3 2 )
) $.

${
  $d k A $.  $d k B $.

  ntp4vc-and32-definition $a |- (
    NTP4VCAnd32 A B
  ) = sum_ k e. ( 0 ... ; 3 1 )
    if (
      (
        ( ( NTP4VCBit32 A k ) = 1 )
        /\
        ( ( NTP4VCBit32 B k ) = 1 )
      ) ,
      ( 2 ^ k ) ,
      0
    ) $.
$}

ntp4vc-rightmost32-definition $a |- (
  NTP4VCRightmost32 A
) = (
  NTP4VCAnd32 A ( NTP4VCNeg32 A )
) $.

${
  $d d x A $.

  ntp4vc-min-elt-definition $a |- (
    NTP4VCMinElt A
  ) = (
    iota_ d e. A A. x e. A d <_ x
  ) $.
$}

${
  $d i r A B C $.

  ntp4vc-state-invariant-definition $a |- (
    NTP4VCStateInvariant A B C
  ) <-> (
    A. i e. ZZ A. r e. A
      (
        (
          (
            0 <_ i
            /\
            i < ; 3 2
          )
          /\
          ( NTP4VCBit32 ( B ` r ) i ) = 1
        )
        <->
        i e. ( C ` r )
      )
  ) $.
$}

${
  $d x y A B C $.

  ntp4vc-state-injective-definition $a |- (
    NTP4VCStateInjective A B C
  ) <-> (
    A. x e. A A. y e. A
      (
        (
          ( B ` x ) = ( B ` y )
          /\
          ( C ` x ) = ( C ` y )
        )
        ->
        x = y
      )
  ) $.
$}

${
  $d i r A B C D $.

  ntp4vc-rightmost-vc-definition $a |- (
    NTP4VCRightmostVC A B C D
  ) <-> (
    (
      A. i e. ZZ
        (
          (
            (
              0 <_ i
              /\
              i < ; 3 2
            )
            /\
            (
              NTP4VCBit32
                ( NTP4VCRightmost32 ( C ` A ) )
                i
            ) = 1
          )
          <->
          i e. { ( NTP4VCMinElt ( D ` A ) ) }
        )
    )
    /\
    A. r e. B
      (
        (
          ( C ` r ) = ( NTP4VCRightmost32 ( C ` A ) )
          /\
          ( D ` r ) = { ( NTP4VCMinElt ( D ` A ) ) }
        )
        ->
        ( D ` r ) = { ( NTP4VCMinElt ( D ` A ) ) }
      )
  ) $.
$}

${
  $d A B C D $.

  $( Source abstract state type and its accessors. $)
  ntp4vc-state-carrier-nonempty $e |- B =/= (/) $.
  ntp4vc-bv-accessor $e |- C e. ( NTP4VCWord32 ^m B ) $.
  ntp4vc-model-accessor $e |- D e. ( NTP4VCFSet ^m B ) $.

  $( Universal source record invariant and extensionality/injectivity law. $)
  ntp4vc-state-invariant $e |- (
    NTP4VCStateInvariant B C D
  ) $.
  ntp4vc-state-injective $e |- (
    NTP4VCStateInjective B C D
  ) $.

  $( Source theorem parameter A=a and its nonempty model-set assumption. $)
  ntp4vc-a-state $e |- A e. B $.
  ntp4vc-a-model-nonempty $e |- ( D ` A ) =/= (/) $.

  ntp4vc-pearl-queens-bv-bits-rightmost-bit-trick-vc $a |- (
    NTP4VCRightmostVC A B C D
  ) $.
$}
