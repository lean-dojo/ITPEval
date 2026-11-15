$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_post_reorder_goal1:
  the push-heap post-reorder verification condition states that the final
  memory and the preceding memory have the same multiset of signed 32-bit
  values over the active heap prefix, under the generated heap-order,
  branch-update, multiset-change, integer-range, memory-validity, linking,
  region, havoc, and parent-index conditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories remain arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCUpdate, NTP4VCSeparated, NTP4VCHavoc,
  NTP4VCHeapParent, NTP4VCValidRD, NTP4VCValidRW, NTP4VCSint32,
  NTP4VCUint32, NTP4VCIsHeap, NTP4VCUnchanged, NTP4VCCount,
  NTP4VCMultisetAdd, NTP4VCMultisetMinus, NTP4VCMultisetRetain,
  NTP4VCMultisetRetainRest, and NTP4VCMultisetUnchanged directly render the
  corresponding source definitions. Heap-parent division specializes the
  source Int.tdiv operation to its fixed positive divisor 2: it uses ceiling
  for a negative numerator and floor otherwise, exactly implementing
  truncation toward zero. Every integer quantifier retains the full source
  domain ZZ.

  The arbitrary map O represents region, membership of allocation map H in
  the arbitrary set P represents linked, Q represents to_uint32, and the
  curried map R represents l_count_1'. The source range and identity laws for
  to_uint32 and all four source counting laws are retained as universally
  quantified scoped hypotheses. Boolean parameters K and M range over the
  exactly two-element Boolean carrier, with 0 representing false.

  The source let bindings are named by NTP4VCA1 through NTP4VCA6,
  NTP4VCX through NTP4VCX3, and NTP4VCM, preserving their original
  dependency order and full-domain function updates. Each proposition-valued
  source if is represented by the equivalent conjunction of its positive-
  branch and negated-branch implications. Splitting the outer source curried
  implication chain into scoped essential hypotheses is bidirectionally
  equivalent for the arbitrary displayed parameters. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCUpdate
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCHeapParent
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCUnchanged NTP4VCCount
  NTP4VCMultisetAdd NTP4VCMultisetMinus
  NTP4VCMultisetRetain NTP4VCMultisetRetainRest
  NTP4VCMultisetUnchanged
  NTP4VCA1 NTP4VCX NTP4VCA2 NTP4VCA3 NTP4VCX1
  NTP4VCA4 NTP4VCX2 NTP4VCA5 NTP4VCM NTP4VCX3 NTP4VCA6
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

ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A B C ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-m-class $a class ( NTP4VCM A B C D ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B C ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B ) $.

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
ntp4vc-multiset-add-syntax
  $a wff ( NTP4VCMultisetAdd A B C D E F ) $.
ntp4vc-multiset-minus-syntax
  $a wff ( NTP4VCMultisetMinus A B C D E F ) $.
ntp4vc-multiset-retain-syntax
  $a wff ( NTP4VCMultisetRetain A B C D E F ) $.
ntp4vc-multiset-retain-rest-syntax
  $a wff ( NTP4VCMultisetRetainRest A B C D E F G ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.

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

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) =
  ( NTP4VCShift A 0 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A ) = ( A - 1 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) =
  ( NTP4VCShift A B ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C ) =
  ( NTP4VCShift A ( C ` ( NTP4VCX B ) ) ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A B C ) =
  ( C ` ( NTP4VCA2 A B ) ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) =
  ( NTP4VCShift A ( NTP4VCX B ) ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C ) =
  ( C ` ( NTP4VCA4 A B ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( NTP4VCShift A B ) $.
ntp4vc-m-def $a |- ( NTP4VCM A B C D ) =
  (
    NTP4VCUpdate
      D
      ( NTP4VCA4 A B )
      ( NTP4VCX1 A C D )
  ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B C ) =
  ( C ` ( NTP4VCA5 A B ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B ) =
  ( NTP4VCShift A B ) $.

${
  $d x y p m n v A B C D E F G H I J K L M N O P Q R $.

  $( Source parameters:
     A=a, B=i_1, C=i_5, D=t_4, E=i_3, F=t_2, G=i, H=t,
     I=i_2, J=i_4, K=p_1, L=t_3, M=p, and N=t_1.
     O is region, P is the extension of linked, Q is to_uint32, and
     R is l_count_1'. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- B e. ZZ $.
  ntp4vc-i5-integer $e |- C e. ZZ $.
  ntp4vc-t4-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i3-integer $e |- E e. ZZ $.
  ntp4vc-t2-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-i2-integer $e |- I e. ZZ $.
  ntp4vc-i4-integer $e |- J e. ZZ $.
  ntp4vc-p1-boolean $e |- ( K = 0 \/ K = 1 ) $.
  ntp4vc-t3-memory $e |- L e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-p-boolean $e |- ( M = 0 \/ M = 1 ) $.
  ntp4vc-t1-memory $e |- N e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- O e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- P C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- Q e. ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- R e.
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
    ( NTP4VCUint32 ( Q ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( Q ` x ) = x ) $.

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
                  ( NTP4VCCount R x p m n v ) = 0
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
                      1 + ( NTP4VCCount R x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount R x p m n v )
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
                      ( NTP4VCCount R x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount R x p m n v )
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
                      ( NTP4VCCount R y p m n v )
                      =
                      ( NTP4VCCount R x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i1-positive $e |- 0 < B $.
  ntp4vc-region-a $e |- ( O ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- H e. P $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 I ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-i5-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA1 A ) B
  ) $.
  ntp4vc-initial-prefix-is-heap $e |- (
    NTP4VCIsHeap D A ( NTP4VCX B )
  ) $.

  ntp4vc-conditional-state $e |- (
    (
      2 <_ B
      ->
      (
        K = 0
        /\
        (
          ( NTP4VCHeapParent ( NTP4VCX B ) ) = C
          /\
          (
            ( NTP4VCValidRD H ( NTP4VCA2 A C ) 1 )
            /\
            (
              ( NTP4VCValidRD H ( NTP4VCA3 A B Q ) 1 )
              /\
              (
                (
                  ( NTP4VCX1 A C D ) < ( NTP4VCX2 A B D )
                  ->
                  (
                    (
                      NTP4VCUpdate
                        F
                        ( NTP4VCA5 A E )
                        ( NTP4VCX2 A B D )
                    )
                    =
                    L
                    /\
                    (
                      ( NTP4VCValidRW H ( NTP4VCA5 A E ) 1 )
                      /\
                      (
                        ( NTP4VCValidRW H ( NTP4VCA3 A B Q ) 1 )
                        /\
                        (
                          (
                            0 < C
                            ->
                            (
                              M = 0
                              /\
                              (
                                E = I
                                /\
                                (
                                  J = I
                                  /\
                                  (
                                    J = E
                                    /\
                                    (
                                      ( NTP4VCHeapParent E ) = G
                                      /\
                                      (
                                        (
                                          NTP4VCHavoc
                                            N
                                            ( NTP4VCM A B C D )
                                            ( NTP4VCA1 A )
                                            B
                                        )
                                        =
                                        F
                                        /\
                                        (
                                          0 <_ E
                                          /\
                                          (
                                            ( NTP4VCX3 A E F )
                                            <
                                            ( NTP4VCX2 A B D )
                                            /\
                                            (
                                              ( 2 + E ) <_ B
                                              /\
                                              (
                                                ( NTP4VCIsHeap F A B )
                                                /\
                                                (
                                                  (
                                                    NTP4VCMultisetAdd
                                                      F
                                                      D
                                                      A
                                                      B
                                                      ( NTP4VCX3 A E F )
                                                      R
                                                  )
                                                  /\
                                                  (
                                                    (
                                                      NTP4VCMultisetMinus
                                                        F
                                                        D
                                                        A
                                                        B
                                                        (
                                                          NTP4VCX2 A B D
                                                        )
                                                        R
                                                    )
                                                    /\
                                                    (
                                                      (
                                                        NTP4VCMultisetRetainRest
                                                          F
                                                          D
                                                          A
                                                          B
                                                          (
                                                            NTP4VCX2 A B D
                                                          )
                                                          (
                                                            NTP4VCX3 A E F
                                                          )
                                                          R
                                                      )
                                                      /\
                                                      (
                                                        E <_ 0
                                                        \/
                                                        (
                                                          (
                                                            NTP4VCX2 A B D
                                                          )
                                                          <_
                                                          (
                                                            F
                                                            `
                                                            (
                                                              NTP4VCA6 A G
                                                            )
                                                          )
                                                          /\
                                                          (
                                                            NTP4VCValidRD
                                                              H
                                                              (
                                                                NTP4VCA6 A G
                                                              )
                                                              1
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
                          /\
                          (
                            -. ( 0 < C )
                            ->
                            (
                              C = E
                              /\
                              ( NTP4VCM A B C D ) = F
                            )
                          )
                        )
                      )
                    )
                  )
                )
                /\
                (
                  -. (
                    ( NTP4VCX1 A C D ) < ( NTP4VCX2 A B D )
                  )
                  ->
                  D = L
                )
              )
            )
          )
        )
      )
    )
    /\
    (
      -. ( 2 <_ B )
      ->
      D = L
    )
  ) $.

  ntp4vc-push-heap-post-reorder-goal1 $a |- (
    NTP4VCMultisetUnchanged L D A 0 B R
  ) $.
$}
