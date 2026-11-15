$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9:
  the pop-heap loop-invariant establishment condition states that the initial
  array value is an upper bound for every value in the active heap prefix,
  under the generated heap-order, maximum-child, integer-range, memory
  validity, linking, region, and parent-index assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCTDiv, NTP4VCHeapParent,
  NTP4VCValidRD, NTP4VCValidRW, NTP4VCSint32, NTP4VCUint32,
  NTP4VCIsHeap, NTP4VCHeapMaximumChild, and NTP4VCUpperBound directly
  expand the corresponding source definitions. Truncating division is toward
  zero, and every integer quantifier retains the full source domain ZZ.

  The arbitrary map F represents region, membership of allocation map E in
  the arbitrary set G represents linked, and H represents to_uint32. Its
  source range and identity laws are retained as scoped hypotheses. The
  source let bindings are expanded as x=A-1, x_1=B(shift(C,x)),
  a_1=shift(C,0), and x_2=B(a_1). Splitting the curried implication chain
  into scoped essential hypotheses is bidirectionally equivalent for the
  arbitrary displayed parameters. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint32Limit NTP4VCUint32Limit NTP4VCMaxParentIndex
  NTP4VCTDiv NTP4VCHeapParent
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCHeapMaximumChild NTP4VCUpperBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-max-parent-index-class $a class NTP4VCMaxParentIndex $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-heap-parent-class $a class ( NTP4VCHeapParent A ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-is-heap-syntax
  $a wff ( NTP4VCIsHeap A B C ) $.
ntp4vc-heap-maximum-child-syntax
  $a wff ( NTP4VCHeapMaximumChild A B C D E ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-max-parent-index-def $a |- NTP4VCMaxParentIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.

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

ntp4vc-heap-parent-def $a |- ( NTP4VCHeapParent A ) =
  ( NTP4VCTDiv ( A - 1 ) 2 ) $.

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

ntp4vc-valid-rw-def $a |- ( ( NTP4VCValidRW A B C ) <->
  (
    0 < C
    ->
    (
      0 < ( NTP4VCBase B )
      /\
      (
        0 <_ ( NTP4VCOffset B )
        /\
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
      )
    )
  )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
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
            ( A ` ( NTP4VCShift B ( NTP4VCHeapParent x ) ) )
          )
        )
      )
  ) $.
$}

ntp4vc-heap-maximum-child-def $a |- (
  ( NTP4VCHeapMaximumChild A B C D E )
  <->
  (
    0 <_ D
    /\
    (
      ( 2 + D ) <_ C
      /\
      (
        (
          D <_ NTP4VCMaxParentIndex
          ->
          ( NTP4VCHeapParent E ) = D
        )
        /\
        (
          (
            ( 2 + ( 1 + ( 2 x. D ) ) ) <_ C
            ->
            (
              A
              `
              ( NTP4VCShift B ( 1 + ( 2 x. D ) ) )
            )
            <_
            ( A ` ( NTP4VCShift B E ) )
          )
          /\
          (
            ( 2 + ( 2 + ( 2 x. D ) ) ) <_ C
            ->
            (
              A
              `
              ( NTP4VCShift B ( 2 + ( 2 x. D ) ) )
            )
            <_
            ( A ` ( NTP4VCShift B E ) )
          )
        )
      )
    )
  )
) $.

${
  $d x A B C D E $.
  ntp4vc-upper-bound-def $a |- (
    ( NTP4VCUpperBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) <_ E
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H $.

  $( Source parameters:
     A=i, B=t_1, C=a, D=i_1, and E=t.
     F is region, G is the extension of linked, and H is to_uint32.
     Source lets are expanded as x=A-1, x_1=B(shift(C,A-1)),
     a_1=shift(C,0), and x_2=B(shift(C,0)). $)

  ntp4vc-i-integer $e |- A e. ZZ $.
  ntp4vc-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- G C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- H e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( H ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( H ` x ) = x ) $.

  ntp4vc-i-positive $e |- 0 < A $.
  ntp4vc-i1-positive $e |- 0 < D $.
  ntp4vc-region-a $e |- ( F ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-last-value-lt-first $e |- (
    ( B ` ( NTP4VCShift C ( A - 1 ) ) )
    <
    ( B ` ( NTP4VCShift C 0 ) )
  ) $.
  ntp4vc-i-at-least-two $e |- 2 <_ A $.
  ntp4vc-linked-allocation $e |- E e. G $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-prefix-is-heap $e |- ( NTP4VCIsHeap B C A ) $.
  ntp4vc-first-value-sint32 $e |- (
    NTP4VCSint32 ( B ` ( NTP4VCShift C 0 ) )
  ) $.
  ntp4vc-root-maximum-child $e |- (
    NTP4VCHeapMaximumChild B C A 0 D
  ) $.
  ntp4vc-first-cell-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift C 0 ) 1
  ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW E ( NTP4VCShift C 0 ) A
  ) $.
  ntp4vc-parent-zero-value-sint32 $e |- (
    NTP4VCSint32
      ( B ` ( NTP4VCShift C ( NTP4VCHeapParent 0 ) ) )
  ) $.
  ntp4vc-last-value-sint32 $e |- (
    NTP4VCSint32 ( B ` ( NTP4VCShift C ( A - 1 ) ) )
  ) $.
  ntp4vc-last-cell-valid-rd $e |- (
    NTP4VCValidRD
      E
      ( NTP4VCShift C ( H ` ( A - 1 ) ) )
      1
  ) $.
  ntp4vc-i1-parent-assumption $e |- (
    ( ( 2 + D ) <_ A ) -> ( NTP4VCHeapParent D ) = 0
  ) $.

  ntp4vc-pop-heap-loop-inv-max-established-goal9 $a |- (
    NTP4VCUpperBound
      B
      C
      0
      A
      ( B ` ( NTP4VCShift C 0 ) )
  ) $.
$}
