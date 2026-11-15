$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/HeapMaximum_Why3_ide_VCHeapMaximum_loop_inv_2_preserved_goal2:
  the heap-maximum loop-invariant preservation condition states that the
  value at a nonnegative index i_2 no greater than i_1 is bounded above by
  the value at index zero, under the generated integer bounds, unsigned-32,
  memory-region, heap, and preceding-prefix upper-bound assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUint32, and NTP4VCIsHeap directly
  expand the corresponding source definitions. NTP4VCTDiv is truncating
  integer division toward zero. Every integer quantifier retains the full
  source domain ZZ, and the memory and region objects are arbitrary total
  integer-valued functions on their respective source domains.

  The source let-bound x is definitionally expanded to the memory value at
  shift(a,0). Splitting the source curried implication chain into scoped
  essential hypotheses is bidirectionally equivalent for the arbitrary
  displayed parameters. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCUint32 NTP4VCIsHeap
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.

ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-is-heap-syntax
  $a wff ( NTP4VCIsHeap A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

${
  $d x A B C $.
  ntp4vc-is-heap-def $a |- (
    ( NTP4VCIsHeap A B C )
    <->
    A. x e. ZZ
      (
        0 < x
        ->
        (
          x < C
          ->
          (
            ( A ` ( NTP4VCShift B x ) )
            <_
            (
              A
              `
              (
                NTP4VCShift
                  B
                  ( NTP4VCTDiv ( x - 1 ) 2 )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d x A B C D E F $.

  $( Source parameters:
     A=t, B=a, C=i, D=i_1, and E=i_2. F is the region function.
     The source let x=t(shift(a,0)) is expanded at each occurrence. $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-region-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-i-positive $e |- 0 < C $.
  ntp4vc-i1-le-i $e |- D <_ C $.
  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-i1-lt-i $e |- D < C $.
  ntp4vc-i2-le-i1 $e |- E <_ D $.
  ntp4vc-i2-nonnegative $e |- 0 <_ E $.
  ntp4vc-region-a $e |- ( F ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-i1-max-index $e |- D <_ NTP4VCMaxIndex $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-prefix-is-heap $e |- ( NTP4VCIsHeap A B C ) $.
  ntp4vc-i1-successor-uint32 $e |- (
    NTP4VCUint32 ( 1 + D )
  ) $.

  ntp4vc-preceding-prefix-upper-bound $e |-
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < D
          ->
          (
            ( A ` ( NTP4VCShift B x ) )
            <_
            ( A ` ( NTP4VCShift B 0 ) )
          )
        )
      ) $.

  ntp4vc-heap-maximum-loop-inv-2-preserved-goal2 $a |- (
    ( A ` ( NTP4VCShift B E ) )
    <_
    ( A ` ( NTP4VCShift B 0 ) )
  ) $.
$}
