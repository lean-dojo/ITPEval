$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_loop_inv_reorder_preserved_goal3:
  the make-heap loop-invariant preservation condition states that, after
  the second havoc update, the half-open prefix ending at two plus the
  current index has the same multiset of signed 32-bit values as the
  original memory, under the generated bounds, linking, memory-validity,
  heap, unchanged-range, and prior multiset assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCUint32, NTP4VCIsHeap, NTP4VCUnchanged, and
  NTP4VCMultisetUnchanged directly expand the corresponding source
  definitions. NTP4VCTDiv is truncating integer division toward zero.
  Every integer quantifier retains the full source domain ZZ, and every
  memory is an arbitrary total function from addresses to integers.

  The arbitrary map H represents region, membership of the allocation map G
  in the arbitrary set J represents linked, and the curried map K represents
  l_count_1'. All four source counting laws are retained as universally
  quantified scoped hypotheses. The source let bindings x, a_1, a_2, and
  a_3 are retained by explicit definitions.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCMaxIndex NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCUnchanged NTP4VCMultisetUnchanged
  NTP4VCCount NTP4VCX NTP4VCA1 NTP4VCA2 NTP4VCA3
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C D E F ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
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
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
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

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
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

${
  $d x A B C D E F $.
  ntp4vc-multiset-unchanged-def $a |- (
    ( NTP4VCMultisetUnchanged A B C D E F )
    <->
    A. x e. ZZ
      (
        ( NTP4VCSint32 x )
        ->
        (
          ( NTP4VCCount F B C D E x )
          =
          ( NTP4VCCount F A C D E x )
        )
      )
  ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( 1 + A ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C D E F ) =
  (
    NTP4VCHavoc
      A
      ( NTP4VCA2 B C D E )
      ( NTP4VCA1 D )
      ( NTP4VCX F )
  ) $.

${
  $d x y p m n v A B C D E F G H J K $.

  $( Source parameters:
     A=i_1, B=a, C=t_1, D=t_3, E=i, F=t_2, and G=t.
     H is region, J is the extension of linked, and K is l_count_1'.
     The source let-bound objects are the explicit NTP4VCX and NTP4VCA*
     definitions above. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-t2-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- K e.
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
                  ( NTP4VCCount K x p m n v ) = 0
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
                      1 + ( NTP4VCCount K x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount K x p m n v )
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
                      ( NTP4VCCount K x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount K x p m n v )
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
                      ( NTP4VCCount K y p m n v )
                      =
                      ( NTP4VCCount K x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i-positive $e |- 0 < E $.
  ntp4vc-i1-positive $e |- 0 < A $.
  ntp4vc-i1-le-i $e |- A <_ E $.
  ntp4vc-i1-lt-i $e |- A < E $.
  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-i1-max-index $e |- A <_ NTP4VCMaxIndex $.
  ntp4vc-linked-allocation $e |- G e. J $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-x-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX A ) ) $.

  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCA1 B ) E
  ) $.
  ntp4vc-extended-prefix-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCA1 B ) ( NTP4VCX A )
  ) $.
  ntp4vc-prefix-is-heap $e |- (
    NTP4VCIsHeap ( NTP4VCA2 C D B E ) B A
  ) $.
  ntp4vc-prefix-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA2 C D B E )
      D
      B
      0
      ( NTP4VCX A )
      K
  ) $.
  ntp4vc-suffix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA2 C D B E )
      D
      B
      ( NTP4VCX A )
      E
  ) $.
  ntp4vc-extended-prefix-is-heap $e |- (
    NTP4VCIsHeap
      ( NTP4VCA3 F C D B E A )
      B
      ( NTP4VCX A )
  ) $.
  ntp4vc-second-update-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA3 F C D B E A )
      ( NTP4VCA2 C D B E )
      B
      0
      ( NTP4VCX A )
      K
  ) $.

  ntp4vc-make-heap-loop-inv-reorder-preserved-goal3 $a |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA3 F C D B E A )
      D
      B
      0
      ( 2 + A )
      K
  ) $.
$}
