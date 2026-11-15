$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/queens_bv_Bits_belowqtvc: the 32-bit below-mask verification
  condition identifies the set bits of a complemented shifted all-ones word
  with the integer interval from zero to the unsigned input. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A source 32-bit word is represented exactly by its unsigned value from zero
  through 2^32-1. NTP4VCBit32 is binary digit extraction on the guarded
  indices zero through 31. NTP4VCShiftL32 is fixed-width logical left shift,
  NTP4VCNot32 is 32-bit complement, and NTP4VCBelow32 is the source expression
  obtained by complementing the all-ones word shifted left by n.

  NTP4VCFSet is the full carrier of finite integer sets, and
  NTP4VCInterval32 n is the half-open integer interval [0,n). B is an
  arbitrary nonempty source state carrier; C and D are respectively its
  32-bit-word and finite-integer-set accessors. NTP4VCStateInvariant and
  NTP4VCStateInjective reproduce the source record invariant and extensional
  injectivity law on every state.

  Expanding NTP4VCBelowVC recovers both source conjuncts with the let-bound
  interval and mask substituted definitionally. The arbitrary state carrier,
  accessors, universal invariant, injectivity law, complete word domain,
  unsigned bound, integer quantifiers, and result quantifier are all retained.
  Every auxiliary $a below is syntax or an explicit faithful definition
  required by the target. The final $a is Metamath's native unproved statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCWord32 NTP4VCFSet NTP4VCBit32
  NTP4VCShiftL32 NTP4VCNot32 NTP4VCBelow32 NTP4VCInterval32
  NTP4VCStateInvariant NTP4VCStateInjective NTP4VCBelowVC
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-fset-syntax $a class NTP4VCFSet $.
ntp4vc-bit32-syntax $a class ( NTP4VCBit32 A B ) $.
ntp4vc-shiftl32-syntax $a class ( NTP4VCShiftL32 A B ) $.
ntp4vc-not32-syntax $a class ( NTP4VCNot32 A ) $.
ntp4vc-below32-syntax $a class ( NTP4VCBelow32 A ) $.
ntp4vc-interval32-syntax $a class ( NTP4VCInterval32 A ) $.
ntp4vc-state-invariant-syntax
  $a wff ( NTP4VCStateInvariant A B C ) $.
ntp4vc-state-injective-syntax
  $a wff ( NTP4VCStateInjective A B C ) $.
ntp4vc-below-vc-syntax
  $a wff ( NTP4VCBelowVC A B C D ) $.

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

ntp4vc-shiftl32-definition $a |- (
  NTP4VCShiftL32 A B
) = (
  ( A x. ( 2 ^ B ) ) mod ( 2 ^ ; 3 2 )
) $.

ntp4vc-not32-definition $a |- (
  NTP4VCNot32 A
) = (
  ( ( 2 ^ ; 3 2 ) - 1 ) - A
) $.

ntp4vc-below32-definition $a |- (
  NTP4VCBelow32 A
) = (
  NTP4VCNot32
    (
      NTP4VCShiftL32
        ( ( 2 ^ ; 3 2 ) - 1 )
        A
    )
) $.

ntp4vc-interval32-definition $a |- (
  NTP4VCInterval32 A
) = (
  0 ..^ A
) $.

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

  ntp4vc-below-vc-definition $a |- (
    NTP4VCBelowVC A B C D
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
            ( NTP4VCBit32 ( NTP4VCBelow32 A ) i ) = 1
          )
          <->
          i e. ( NTP4VCInterval32 A )
        )
    )
    /\
    A. r e. B
      (
        (
          ( C ` r ) = ( NTP4VCBelow32 A )
          /\
          ( D ` r ) = ( NTP4VCInterval32 A )
        )
        ->
        ( D ` r ) = ( NTP4VCInterval32 A )
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

  $( Source theorem parameter A=n and its unsigned bound. $)
  ntp4vc-n-word32 $e |- A e. NTP4VCWord32 $.
  ntp4vc-n-at-most-32 $e |- A <_ ; 3 2 $.

  ntp4vc-pearl-queens-bv-bits-below-vc $a |- (
    NTP4VCBelowVC A B C D
  ) $.
$}
