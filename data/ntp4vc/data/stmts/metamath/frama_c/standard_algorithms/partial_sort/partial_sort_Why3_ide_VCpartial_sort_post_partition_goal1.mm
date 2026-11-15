$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1:
  the partial-sort post-partition verification condition states that the
  final memory is partitioned at i_1 over the half-open range ending at i,
  under the generated integer bounds, memory-region, linking, unsigned-32,
  signed-32, write-validity, conditional havoc, sorting, heap, multiset,
  unchanged-range, upper-bound, and lower-bound assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories are arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRW, NTP4VCSint32,
  NTP4VCUint32, NTP4VCSorted, NTP4VCIsHeap, NTP4VCUnchanged,
  NTP4VCMultisetUnchanged, NTP4VCUpperBound, NTP4VCLowerBound, and
  NTP4VCPartition directly expand the corresponding source definitions.
  NTP4VCTDiv is truncating integer division toward zero.

  The source Boolean p is represented by the exactly two-element carrier
  { 0 , 1 }, with false represented by 0. The arbitrary map O represents
  region, membership of the allocation map H in the arbitrary set P
  represents linked, and the curried map Q represents l_count_1'. All four
  source counting laws are retained as universally quantified scoped
  hypotheses. The source let bindings a_1, x, and a_2 are retained by
  explicit definitions. Every integer quantifier retains the full source
  domain ZZ.

  The proposition-valued if is rendered by the equivalent guarded
  disjunction (condition and then-branch) or (negated condition and
  else-branch). Splitting the source curried implication chain into scoped
  essential hypotheses is bidirectionally equivalent for the arbitrary
  displayed parameters. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCSorted NTP4VCIsHeap NTP4VCUnchanged
  NTP4VCMultisetUnchanged NTP4VCUpperBound NTP4VCLowerBound
  NTP4VCPartition NTP4VCCount
  NTP4VCA1 NTP4VCX NTP4VCA2
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
ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-is-heap-syntax
  $a wff ( NTP4VCIsHeap A B C ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-partition-syntax
  $a wff ( NTP4VCPartition A B C D ) $.

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

${
  $d x y A B C D $.
  ntp4vc-partition-def $a |- (
    ( NTP4VCPartition A B C D )
    <->
    (
      0 <_ C
      ->
      (
        C <_ D
        ->
        A. x e. ZZ
          A. y e. ZZ
            (
              C <_ y
              ->
              (
                y < D
                ->
                (
                  0 <_ x
                  ->
                  (
                    x < C
                    ->
                    (
                      ( A ` ( NTP4VCShift B x ) )
                      <_
                      ( A ` ( NTP4VCShift B y ) )
                    )
                  )
                )
              )
            )
      )
    )
  ) $.
$}

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` ( NTP4VCA1 B ) ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.

${
  $d x y p m n v A B C D E F G H I J K L M N O P Q $.

  $( Source parameters:
     A=a, B=t_6, C=t_3, D=t_5, E=i_2, F=i_1, G=i, H=t,
     I=p, J=t_1, K=t_2, L=t_8, M=t_4, and N=t_7.
     O is region, P is the extension of linked, and Q is l_count_1'.
     The source lets are NTP4VCA1(A)=shift(A,0),
     NTP4VCX(B,A)=B(shift(A,0)), and
     NTP4VCA2(C,D,A,E)=havoc(C,D,shift(A,0),E). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t6-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t5-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-p-boolean $e |- I e. { 0 , 1 } $.
  ntp4vc-t1-allocation-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-t2-memory $e |- K e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t8-memory $e |- L e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t4-memory $e |- M e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t7-memory $e |- N e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- P C_ ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- Q e.
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
                  ( NTP4VCCount Q x p m n v ) = 0
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
                      1 + ( NTP4VCCount Q x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount Q x p m n v )
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
                      ( NTP4VCCount Q x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount Q x p m n v )
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
                      ( NTP4VCCount Q y p m n v )
                      =
                      ( NTP4VCCount Q x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i1-le-i $e |- F <_ G $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-region-a $e |- ( O ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- H e. P $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-t5-first-value-sint32 $e |- (
    NTP4VCSint32 ( D ` ( NTP4VCA1 A ) )
  ) $.
  ntp4vc-x-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCX B A )
  ) $.
  ntp4vc-range-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA1 A ) G
  ) $.

  ntp4vc-post-partition-branch $e |- (
    (
      0 < F
      /\
      (
        I = 0
        /\
        (
          J = H
          /\
          (
            ( NTP4VCHavoc K L ( NTP4VCA1 A ) F ) = D
            /\
            (
              ( NTP4VCHavoc C D ( NTP4VCA1 A ) G ) = B
              /\
              (
                (
                  NTP4VCHavoc
                    M
                    ( NTP4VCA2 C D A E )
                    ( NTP4VCA1 A )
                    F
                )
                =
                N
                /\
                (
                  E <_ G
                  /\
                  (
                    G <_ E
                    /\
                    (
                      F <_ E
                      /\
                      (
                        ( NTP4VCSorted N A 0 F )
                        /\
                        (
                          ( NTP4VCIsHeap D A F )
                          /\
                          (
                            ( NTP4VCIsHeap B A F )
                            /\
                            (
                              (
                                NTP4VCMultisetUnchanged
                                  D
                                  L
                                  A
                                  0
                                  F
                                  Q
                              )
                              /\
                              (
                                (
                                  NTP4VCMultisetUnchanged
                                    B
                                    L
                                    A
                                    0
                                    E
                                    Q
                                )
                                /\
                                (
                                  ( NTP4VCUnchanged B L A E G )
                                  /\
                                  (
                                    (
                                      NTP4VCValidRW
                                        J
                                        ( NTP4VCA1 A )
                                        F
                                    )
                                    /\
                                    (
                                      (
                                        NTP4VCUpperBound
                                          B
                                          A
                                          0
                                          F
                                          ( NTP4VCX B A )
                                      )
                                      /\
                                      (
                                        (
                                          NTP4VCLowerBound
                                            B
                                            A
                                            F
                                            E
                                            ( NTP4VCX B A )
                                        )
                                        /\
                                        (
                                          NTP4VCMultisetUnchanged
                                            N
                                            ( NTP4VCA2 C D A E )
                                            A
                                            0
                                            F
                                            Q
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    \/
    (
      -. ( 0 < F )
      /\
      L = N
    )
  ) $.

  ntp4vc-partial-sort-post-partition-goal1 $a |- (
    NTP4VCPartition N A F G
  ) $.
$}
