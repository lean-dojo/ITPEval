$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/LowerBoundShift_Why3_ide_VCLowerBoundShift_post_goal0:
  the lower-bound-shift verification condition transfers an integer lower
  bound from a shifted half-open address interval to the corresponding
  unshifted interval, under the generated memory-region, integer-range, and
  addition-bound assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint32, NTP4VCSint32, and
  NTP4VCLowerBound directly expand the corresponding source definitions.
  The memory map F has the full source domain addr -> int, and every index in
  NTP4VCLowerBound is quantified over all integers.

  The arbitrary integer-valued map G represents the imported source region
  function without adding any laws. The source let-bound value
  x = i_1 + i_3 is expanded at both uses. Splitting the source curried
  implication chain into scoped essential hypotheses is bidirectionally
  equivalent for the arbitrary displayed parameters. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCUint32Max NTP4VCSint32Limit
  NTP4VCUint32 NTP4VCSint32 NTP4VCLowerBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-uint32-max-class $a class NTP4VCUint32Max $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.

ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-uint32-max-def $a |- NTP4VCUint32Max =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-lower-bound-def $a |- (
    ( NTP4VCLowerBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          E <_ ( A ` ( NTP4VCShift B x ) )
        )
      )
  ) $.
$}

${
  $( Source parameters:
     A=i_1, B=i_3, C=a, D=i_2, E=i, and F=t.
     G is the imported region function. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i3-integer $e |- B e. ZZ $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-value-integer $e |- E e. ZZ $.
  ntp4vc-memory-map $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-shifted-upper-bound $e |- ( A + B ) <_ NTP4VCUint32Max $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-value-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-shifted-lower-bound $e |- (
    NTP4VCLowerBound F ( NTP4VCShift C B ) D A E
  ) $.

  ntp4vc-lower-bound-shift-post-goal0 $a |- (
    NTP4VCLowerBound F C ( D + B ) ( A + B ) E
  ) $.
$}
