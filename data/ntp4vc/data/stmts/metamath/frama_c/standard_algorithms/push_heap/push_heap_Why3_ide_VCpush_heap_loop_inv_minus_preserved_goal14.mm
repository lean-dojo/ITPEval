$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_minus_preserved_goal14:
  the push-heap loop-invariant preservation condition states that the
  update moving the current parent value to index i_1 preserves removal of
  one occurrence of the original last-index value from the active heap
  prefix, under the generated heap-order, multiset, integer-range,
  memory-validity, linking, region, and parent-index assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories remain arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCUpdate, NTP4VCSeparated, NTP4VCHavoc,
  NTP4VCHeapParent, NTP4VCValidRD, NTP4VCValidRW, NTP4VCSint32,
  NTP4VCUint32, NTP4VCIsHeap, NTP4VCUnchanged, NTP4VCCount,
  NTP4VCMultisetMinus, NTP4VCMultisetAdd, NTP4VCMultisetRetain, and
  NTP4VCMultisetRetainRest directly render the corresponding source
  definitions.
  Heap-parent division specializes the source Int.tdiv operation to its fixed
  positive divisor 2: it uses ceiling for a negative numerator and floor
  otherwise, exactly implementing truncation toward zero. Every integer
  quantifier retains the full source domain ZZ.

  The arbitrary map G represents region, membership of allocation map F in
  the arbitrary set H represents linked, I represents to_uint32, and the
  curried map J represents l_count_1'. The source range and identity laws for
  to_uint32 and all four source counting laws are retained as universally
  quantified scoped hypotheses.

  The source let bindings are named by NTP4VCX through NTP4VCA10 and preserve
  their original dependency order, including the full-domain update of t_2
  at the last active index, the havoc of the active prefix, and the final
  full-domain update at index i_1. Splitting the source curried implication
  chain into scoped essential hypotheses is bidirectionally equivalent for
  the arbitrary displayed parameters. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCUpdate
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCHeapParent
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCUnchanged NTP4VCCount
  NTP4VCMultisetMinus NTP4VCMultisetAdd
  NTP4VCMultisetRetain NTP4VCMultisetRetainRest
  NTP4VCX NTP4VCX1 NTP4VCA1 NTP4VCX2 NTP4VCA2 NTP4VCX3
  NTP4VCM NTP4VCA3 NTP4VCA4 NTP4VCA5 NTP4VCA6 NTP4VCX4
  NTP4VCA7 NTP4VCA8 NTP4VCA9 NTP4VCA10
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-heap-parent-class $a class ( NTP4VCHeapParent A ) $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B C ) $.
ntp4vc-m-class $a class ( NTP4VCM A B C ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B C D E ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B C ) $.
ntp4vc-a10-class $a class ( NTP4VCA10 A B C D E ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
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
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-minus-syntax
  $a wff ( NTP4VCMultisetMinus A B C D E F ) $.
ntp4vc-multiset-add-syntax
  $a wff ( NTP4VCMultisetAdd A B C D E F ) $.
ntp4vc-multiset-retain-syntax
  $a wff ( NTP4VCMultisetRetain A B C D E F ) $.
ntp4vc-multiset-retain-rest-syntax
  $a wff ( NTP4VCMultisetRetainRest A B C D E F G ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-separated-def $a |- ( ( NTP4VCSeparated A B C D ) <->
  (
    B <_ 0
    \/
    (
      D <_ 0
      \/
      (
        ( NTP4VCBase A ) =/= ( NTP4VCBase C )
        \/
        (
          ( ( NTP4VCOffset C ) + D ) <_ ( NTP4VCOffset A )
          \/
          ( ( NTP4VCOffset A ) + B ) <_ ( NTP4VCOffset C )
        )
      )
    )
  )
) $.

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

${
  $d x A B C D $.
  ntp4vc-havoc-def $a |- ( NTP4VCHavoc A B C D ) =
    (
      x e. NTP4VCAddr |->
        if
        (
          ( NTP4VCSeparated x 1 C D ) ,
          ( B ` x ) ,
          ( A ` x )
        )
    ) $.
$}

ntp4vc-heap-parent-def $a |- ( NTP4VCHeapParent A ) =
  if (
    ( A - 1 ) < 0 ,
    ( |^ ` ( ( A - 1 ) / 2 ) ) ,
    ( |_ ` ( ( A - 1 ) / 2 ) )
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

ntp4vc-count-def $a |- ( NTP4VCCount A B C D E F ) =
  ( ( ( ( ( A ` B ) ` C ) ` D ) ` E ) ` F ) $.

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

${
  $d x A B C D E $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D E )
    <->
    A. x e. ZZ
      (
        D <_ x
        ->
        (
          x < E
          ->
          ( B ` ( NTP4VCShift C x ) )
          =
          ( A ` ( NTP4VCShift C x ) )
        )
      )
  ) $.
$}

ntp4vc-multiset-add-def $a |- (
  ( NTP4VCMultisetAdd A B C D E F )
  <->
  (
    1 + ( NTP4VCCount F B C 0 D E )
  )
  =
  ( NTP4VCCount F A C 0 D E )
) $.

ntp4vc-multiset-minus-def $a |- (
  ( NTP4VCMultisetMinus A B C D E F )
  <->
  (
    1 + ( NTP4VCCount F A C 0 D E )
  )
  =
  ( NTP4VCCount F B C 0 D E )
) $.

ntp4vc-multiset-retain-def $a |- (
  ( NTP4VCMultisetRetain A B C D E F )
  <->
  ( NTP4VCCount F B C 0 D E )
  =
  ( NTP4VCCount F A C 0 D E )
) $.

${
  $d x A B C D E F G $.
  ntp4vc-multiset-retain-rest-def $a |- (
    ( NTP4VCMultisetRetainRest A B C D E F G )
    <->
    A. x e. ZZ
      (
        x =/= E
        ->
        (
          x =/= F
          ->
          (
            ( NTP4VCSint32 x )
            ->
            ( NTP4VCMultisetRetain A B C D x G )
          )
        )
      )
  ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( A - 1 ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A ) =
  ( NTP4VCHeapParent ( NTP4VCX A ) ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A B ) =
  ( NTP4VCShift B ( NTP4VCX1 A ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  ( C ` ( NTP4VCA1 A B ) ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) =
  ( NTP4VCShift B ( NTP4VCX A ) ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B C ) =
  ( C ` ( NTP4VCA2 A B ) ) $.
ntp4vc-m-def $a |- ( NTP4VCM A B C ) =
  (
    NTP4VCUpdate
      C
      ( NTP4VCA2 A B )
      ( NTP4VCX2 A B C )
  ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) =
  ( NTP4VCShift A 0 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D ) =
  (
    NTP4VCHavoc
      D
      ( NTP4VCM A B C )
      ( NTP4VCA3 B )
      A
  ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( NTP4VCShift A B ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E ) =
  ( ( NTP4VCA4 A B C D ) ` ( NTP4VCA5 B E ) ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A ) =
  ( NTP4VCHeapParent A ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A B ) =
  ( NTP4VCShift A ( NTP4VCX4 B ) ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B C D E ) =
  ( ( NTP4VCA4 A B C D ) ` ( NTP4VCA7 B E ) ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B C ) =
  ( NTP4VCShift B ( C ` ( NTP4VCX A ) ) ) $.
ntp4vc-a10-def $a |- ( NTP4VCA10 A B C D E ) =
  (
    NTP4VCUpdate
      ( NTP4VCA4 A B C D )
      ( NTP4VCA5 B E )
      ( NTP4VCA8 A B C D E )
  ) $.

${
  $d x y p m n v A B C D E F G H I J $.

  $( Source parameters:
     A=i, B=a, C=t_2, D=t_1, E=i_1, and F=t.
     G is region, H is the extension of linked, I is to_uint32,
     and J is l_count_1'. $)

  ntp4vc-i-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t2-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t1-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- J e.
    (
      (
        (
          (
            ( ZZ ^m ZZ )
            ^m
            ZZ
          )
          ^m
          ZZ
        )
        ^m
        NTP4VCAddr
      )
      ^m
      ( ZZ ^m NTP4VCAddr )
    ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( I ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( I ` x ) = x ) $.

  ntp4vc-count-section-empty $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                n <_ m
                ->
                (
                  ( NTP4VCSint32 v )
                  ->
                  ( NTP4VCCount J x p m n v ) = 0
                )
              ) $.

  ntp4vc-count-section-hit $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift p ( n - 1 ) ) ) = v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      1 + ( NTP4VCCount J x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount J x p m n v )
                  )
                )
              ) $.

  ntp4vc-count-section-miss $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift p ( n - 1 ) ) ) =/= v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      ( NTP4VCCount J x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount J x p m n v )
                    )
                  )
                )
              ) $.

  ntp4vc-count-section-read $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. ( ZZ ^m NTP4VCAddr )
        A. p e. NTP4VCAddr
          A. m e. ZZ
            A. n e. ZZ
              A. v e. ZZ
                (
                  ( NTP4VCSint32 v )
                  ->
                  (
                    ( NTP4VCUnchanged x y p m n )
                    ->
                    (
                      ( NTP4VCCount J y p m n v )
                      =
                      ( NTP4VCCount J x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i-positive $e |- 0 < A $.
  ntp4vc-i1-positive $e |- 0 < E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ E $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-parent-positive $e |- 0 < ( NTP4VCX1 A ) $.
  ntp4vc-parent-value-lt-last $e |- (
    ( NTP4VCX2 A B C ) < ( NTP4VCX3 A B C )
  ) $.
  ntp4vc-i1-value-lt-last $e |- (
    ( NTP4VCA6 A B C D E ) < ( NTP4VCX3 A B C )
  ) $.
  ntp4vc-i1-value-lt-parent-value $e |- (
    ( NTP4VCA6 A B C D E ) < ( NTP4VCA8 A B C D E )
  ) $.
  ntp4vc-i1-parent-value-lt-last $e |- (
    ( NTP4VCA8 A B C D E ) < ( NTP4VCX3 A B C )
  ) $.
  ntp4vc-i-at-least-two $e |- 2 <_ A $.
  ntp4vc-i1-upper-bound $e |- ( 2 + E ) <_ A $.
  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i1-parent-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX4 E )
  ) $.
  ntp4vc-i1-cell-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA5 B E ) 1
  ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW F ( NTP4VCA3 B ) A
  ) $.
  ntp4vc-i1-cell-valid-rw $e |- (
    NTP4VCValidRW F ( NTP4VCA5 B E ) 1
  ) $.
  ntp4vc-parent-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX1 A )
  ) $.
  ntp4vc-prefix-is-heap $e |- (
    NTP4VCIsHeap C B ( NTP4VCX A )
  ) $.
  ntp4vc-i1-parent-cell-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA7 B E ) 1
  ) $.
  ntp4vc-grandparent-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCHeapParent ( NTP4VCX1 A ) )
  ) $.
  ntp4vc-last-value-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX3 A B C )
  ) $.
  ntp4vc-parent-value-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX2 A B C )
  ) $.
  ntp4vc-last-cell-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA9 A B I ) 1
  ) $.
  ntp4vc-parent-cell-valid-rd $e |- (
    NTP4VCValidRD F ( NTP4VCA1 A B ) 1
  ) $.
  ntp4vc-last-cell-valid-rw $e |- (
    NTP4VCValidRW F ( NTP4VCA9 A B I ) 1
  ) $.
  ntp4vc-updated-parent-value-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCM A B C ) ` ( NTP4VCA1 A B ) )
  ) $.
  ntp4vc-i1-value-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA6 A B C D E )
  ) $.
  ntp4vc-i1-parent-value-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA8 A B C D E )
  ) $.
  ntp4vc-updated-prefix-is-heap $e |- (
    NTP4VCIsHeap ( NTP4VCA4 A B C D ) B A
  ) $.
  ntp4vc-final-parent-value-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCA10 A B C D E ) ` ( NTP4VCA7 B E ) )
  ) $.
  ntp4vc-last-value-removed $e |- (
    NTP4VCMultisetMinus
      ( NTP4VCA4 A B C D )
      C
      B
      A
      ( NTP4VCX3 A B C )
      J
  ) $.
  ntp4vc-i1-value-added $e |- (
    NTP4VCMultisetAdd
      ( NTP4VCA4 A B C D )
      C
      B
      A
      ( NTP4VCA6 A B C D E )
      J
  ) $.
  ntp4vc-other-values-retained $e |- (
    NTP4VCMultisetRetainRest
      ( NTP4VCA4 A B C D )
      C
      B
      A
      ( NTP4VCX3 A B C )
      ( NTP4VCA6 A B C D E )
      J
  ) $.

  ntp4vc-push-heap-loop-inv-minus-preserved-goal14 $a |- (
    NTP4VCMultisetMinus
      ( NTP4VCA10 A B C D E )
      C
      B
      A
      ( NTP4VCX3 A B C )
      J
  ) $.
$}
