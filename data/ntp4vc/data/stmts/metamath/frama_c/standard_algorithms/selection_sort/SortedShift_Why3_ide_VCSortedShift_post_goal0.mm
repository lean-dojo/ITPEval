$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/SortedShift_Why3_ide_VCSortedShift_post_goal0:
  the sorted-shift verification condition states that a sorted half-open
  integer-indexed memory segment remains sorted after shifting its base by
  the lower endpoint and rebasing the segment to start at zero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint32, and NTP4VCSorted directly
  expand the corresponding source definitions. Every index quantifier ranges
  over the full integer domain ZZ, and the memory remains an arbitrary total
  function from addresses to integers.

  The arbitrary integer-valued map E represents the source region function.
  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCUint32 NTP4VCSorted
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.

ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

${
  $d x y A B C D $.
  ntp4vc-sorted-def $a |- (
    ( NTP4VCSorted A B C D )
    <->
    A. x e. ZZ
      A. y e. ZZ
        (
          y < D
          ->
          (
            C <_ x
            ->
            (
              x < y
              ->
              ( A ` ( NTP4VCShift B x ) )
              <_
              ( A ` ( NTP4VCShift B y ) )
            )
          )
        )
  ) $.
$}

${
  $d x y A B C D E $.

  $( Source parameters: A=i_1, B=i, C=a, and D=t.
     E is the arbitrary source region function. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- E e. ( ZZ ^m ZZ ) $.

  ntp4vc-i1-le-i $e |- A <_ B $.
  ntp4vc-region-a $e |- ( E ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-segment-sorted $e |- ( NTP4VCSorted D C A B ) $.

  ntp4vc-sorted-shift-post-goal0 $a |- (
    NTP4VCSorted D ( NTP4VCShift C A ) 0 ( B - A )
  ) $.
$}
