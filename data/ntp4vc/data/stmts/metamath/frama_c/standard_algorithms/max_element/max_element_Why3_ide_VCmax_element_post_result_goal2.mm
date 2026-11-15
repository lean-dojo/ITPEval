$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/max_element/max_element_Why3_ide_VCmax_element_post_result_goal2:
  the max-element post-result verification condition states that the result
  index is nonnegative, under the generated nonpositivity, unsigned-32,
  memory-region, linking, and read-validity assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint32, and NTP4VCValidRD directly
  expand the corresponding source definitions. The arbitrary integer-valued
  map D represents the source region function, and membership of the
  allocation map C in the arbitrary set E represents linked. Thus the source
  integer, address, and function domains and all five assumptions are
  retained without adding laws for the imported region or linked symbols.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCUint32 NTP4VCValidRD
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.

ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.

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

ntp4vc-valid-rd-def $a |- ( ( NTP4VCValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NTP4VCBase B ) =/= 0
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
) $.

${
  $( Source parameters: A=i, B=a, and C=t. D is region, and E is the
     extension of linked. $)

  ntp4vc-i-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- C e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- D e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- E C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonpositive $e |- A <_ 0 $.
  ntp4vc-region-a $e |- ( D ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- C e. E $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD C ( NTP4VCShift B 0 ) A
  ) $.

  ntp4vc-max-element-post-result-goal2 $a |- 0 <_ A $.
$}
