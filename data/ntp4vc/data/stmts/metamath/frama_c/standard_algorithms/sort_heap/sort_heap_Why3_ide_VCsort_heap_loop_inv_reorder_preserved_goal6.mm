$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/sort_heap/sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_preserved_goal6:
  the sort-heap loop-invariant preservation condition states that the second
  havoced memory has the same multiset of signed 32-bit values as the original
  memory over the full half-open range, under the generated bounds, linking,
  memory-validity, heap, sortedness, lower-bound, maximum-element,
  unchanged-range, and prior multiset assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCUint32, NTP4VCIsHeap, NTP4VCSorted,
  NTP4VCUnchanged, NTP4VCMultisetUnchanged, NTP4VCLowerBound, and
  NTP4VCMaxElement directly expand the corresponding source definitions.
  NTP4VCTDiv is truncating integer division toward zero. Every integer
  quantifier retains the full source domain ZZ, and every memory is an
  arbitrary total function from addresses to integers.

  The arbitrary map H represents region, membership of the allocation map G
  in the arbitrary set I represents linked, and the curried map J represents
  l_count_1'. All four source counting laws are retained as universally
  quantified scoped hypotheses. The source let bindings a_1 through a_5 and
  x are retained by explicit definitions.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCSorted NTP4VCUnchanged
  NTP4VCMultisetUnchanged NTP4VCUpperBound NTP4VCLowerBound
  NTP4VCMaxElement NTP4VCCount
  NTP4VCA1 NTP4VCA2 NTP4VCA3 NTP4VCX NTP4VCA4 NTP4VCA5
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-is-heap-syntax $a wff ( NTP4VCIsHeap A B C ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-max-element-syntax
  $a wff ( NTP4VCMaxElement A B C D ) $.

ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C D E F ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D E F ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D ) $.

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
  $d x y A B C D $.
  ntp4vc-sorted-def $a |- (
    ( NTP4VCSorted A B C D )
    <->
    A. x e. ZZ A. y e. ZZ
      (
        y < D
        ->
        (
          C <_ x
          ->
          (
            x < y
            ->
            (
              ( A ` ( NTP4VCShift B x ) )
              <_
              ( A ` ( NTP4VCShift B y ) )
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
  $d x A B C D E $.
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

ntp4vc-max-element-def $a |- (
  ( NTP4VCMaxElement A B C D )
  <->
  (
    0 <_ D
    /\
    (
      D < C
      /\
      (
        NTP4VCUpperBound
          A B 0 C ( A ` ( NTP4VCShift B D ) )
      )
    )
  )
) $.

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C D E F ) =
  (
    NTP4VCHavoc
      A
      ( NTP4VCA2 B C D E )
      ( NTP4VCA1 D )
      F
  ) $.
ntp4vc-x-def $a |- ( NTP4VCX A ) = ( A - 1 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D E F ) =
  (
    ( NTP4VCA3 A B C D E F )
    `
    ( NTP4VCShift D ( NTP4VCX F ) )
  ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D ) =
  ( ( NTP4VCA2 A B C D ) ` ( NTP4VCA1 C ) ) $.

${
  $d x y p m n v A B C D E F G H I J $.

  $( Source parameters:
     A=a, B=t_1, C=t_3, D=i, E=t_2, F=i_1, and G=t.
     H is region, I is the extension of linked, and J is l_count_1'.
     The source let-bound objects are the explicit NTP4VCA* and NTP4VCX
     definitions above. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-t2-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
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

  ntp4vc-a4-equals-a5 $e |- (
    ( NTP4VCA4 E B C A D F )
    =
    ( NTP4VCA5 B C A D )
  ) $.
  ntp4vc-i1-positive $e |- 0 < F $.
  ntp4vc-i1-le-i $e |- F <_ D $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-two-le-i1 $e |- 2 <_ F $.
  ntp4vc-linked-allocation $e |- G e. I $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-original-is-heap $e |- ( NTP4VCIsHeap C A D ) $.
  ntp4vc-original-first-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCA1 A ) )
  ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCA1 A ) D
  ) $.
  ntp4vc-a5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 B C A D )
  ) $.
  ntp4vc-first-update-is-heap $e |- (
    NTP4VCIsHeap ( NTP4VCA2 B C A D ) A F
  ) $.
  ntp4vc-first-update-sorted-suffix $e |- (
    NTP4VCSorted ( NTP4VCA2 B C A D ) A F D
  ) $.
  ntp4vc-first-update-original-multiset $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA2 B C A D )
      C
      A
      0
      D
      J
  ) $.
  ntp4vc-first-update-lower-bound $e |- (
    NTP4VCLowerBound
      ( NTP4VCA2 B C A D )
      A
      F
      D
      ( NTP4VCA5 B C A D )
  ) $.
  ntp4vc-second-update-first-sint32 $e |- (
    NTP4VCSint32
      ( ( NTP4VCA3 E B C A D F ) ` ( NTP4VCA1 A ) )
  ) $.
  ntp4vc-a4-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA4 E B C A D F )
  ) $.
  ntp4vc-second-update-is-heap $e |- (
    NTP4VCIsHeap
      ( NTP4VCA3 E B C A D F )
      A
      ( NTP4VCX F )
  ) $.
  ntp4vc-second-update-max-element $e |- (
    NTP4VCMaxElement
      ( NTP4VCA3 E B C A D F )
      A
      F
      ( NTP4VCX F )
  ) $.
  ntp4vc-second-first-unchanged-suffix $e |- (
    NTP4VCUnchanged
      ( NTP4VCA3 E B C A D F )
      ( NTP4VCA2 B C A D )
      A
      F
      D
  ) $.
  ntp4vc-second-first-prefix-multiset $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA3 E B C A D F )
      ( NTP4VCA2 B C A D )
      A
      0
      F
      J
  ) $.

  ntp4vc-sort-heap-loop-inv-reorder-preserved-goal6 $a |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA3 E B C A D F )
      C
      A
      0
      D
      J
  ) $.
$}
