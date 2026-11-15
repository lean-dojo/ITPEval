$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_result_goal1:
  the pop-heap post-result verification condition states that the value in
  the final memory at the last active heap index equals the initial root
  value, under the generated heap, maximum-child, upper-bound, integer-range,
  memory-validity, linking, region, havoc, and update conditions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories are arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCSeparated, NTP4VCHavoc, NTP4VCUpdate,
  NTP4VCTDiv, NTP4VCHeapParent, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCUint32, NTP4VCIsHeap,
  NTP4VCHeapMaximumChild, NTP4VCUpperBound, and NTP4VCUnchanged directly
  expand the corresponding source definitions. Every integer quantifier
  retains the full source domain ZZ.

  The arbitrary map N represents region, membership of the allocation map G
  in the arbitrary set O represents linked, P represents to_uint32, and the
  curried map Q represents l_count_2_. The source range and identity laws for
  to_uint32 and all four source counting laws are retained as universally
  quantified scoped hypotheses. Boolean parameters J and K range over the
  two-element Boolean carrier, with 0 representing false.

  The source let bindings are expanded inline as a_1=shift(A,0),
  x=B(a_1), x_1=C-1, a_2=shift(A,x_1),
  x_2=I(a_2), a_3=shift(A,P(x_1)), a_4=shift(A,D), x_3=E(a_2), and
  a_5=shift(A,F). Each proposition-valued conditional is rendered by the
  equivalent pair of implications for its true and false branches. Splitting
  the outer curried implication chain into scoped essential hypotheses is
  bidirectionally equivalent for the arbitrary displayed parameters. The
  conclusion is I(a_2)=B(a_1). The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc NTP4VCUpdate
  NTP4VCSint32Limit NTP4VCUint32Limit NTP4VCMaxParentIndex
  NTP4VCTDiv NTP4VCHeapParent
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCHeapMaximumChild NTP4VCUpperBound
  NTP4VCUnchanged NTP4VCCount
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-max-parent-index-class $a class NTP4VCMaxParentIndex $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-heap-parent-class $a class ( NTP4VCHeapParent A ) $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

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
ntp4vc-heap-maximum-child-syntax
  $a wff ( NTP4VCHeapMaximumChild A B C D E ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.

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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

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
  $d x y p m n v A B C D E F G H I J K L M N O P Q $.

  $( Source parameters:
     A=a, B=t_5, C=i, D=i_1, E=t_3, F=i_3, G=t, H=i_2,
     I=t_4, J=p, K=p_1, L=t_1, and M=t_2.
     N is region, O is the extension of linked, P is to_uint32, and
     Q is l_count_2_. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t5-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-t3-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i3-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-i2-integer $e |- H e. ZZ $.
  ntp4vc-t4-memory $e |- I e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-p-boolean $e |- ( J = 0 \/ J = 1 ) $.
  ntp4vc-p1-boolean $e |- ( K = 0 \/ K = 1 ) $.
  ntp4vc-t1-allocation-map $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-t2-memory $e |- M e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- O C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- P e. ( ZZ ^m ZZ ) $.
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

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( P ` x ) ) $.
  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    ( ( NTP4VCUint32 x ) -> ( P ` x ) = x ) $.

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

  ntp4vc-i-positive $e |- 0 < C $.
  ntp4vc-region-a $e |- ( N ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- G e. O $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-initial-is-heap $e |- ( NTP4VCIsHeap B A C ) $.
  ntp4vc-root-value-sint32 $e |- (
    NTP4VCSint32 ( B ` ( NTP4VCShift A 0 ) )
  ) $.
  ntp4vc-initial-prefix-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCShift A 0 ) C
  ) $.
  ntp4vc-final-last-value-sint32 $e |- (
    NTP4VCSint32 ( I ` ( NTP4VCShift A ( C - 1 ) ) )
  ) $.

  ntp4vc-conditional-state $e |- (
    (
      2 <_ C
      ->
      (
        ( NTP4VCValidRD G ( NTP4VCShift A 0 ) 1 )
        /\
        (
          (
            NTP4VCValidRD
              G
              ( NTP4VCShift A ( P ` ( C - 1 ) ) )
              1
          )
          /\
          (
            (
              ( B ` ( NTP4VCShift A ( C - 1 ) ) )
              <
              ( B ` ( NTP4VCShift A 0 ) )
              ->
              (
                J = 0
                /\
                (
                  K = 0
                  /\
                  (
                    L = G
                    /\
                    (
                      (
                        NTP4VCHavoc
                          M
                          B
                          ( NTP4VCShift A 0 )
                          ( C - 1 )
                      )
                      =
                      E
                      /\
                      (
                        (
                          NTP4VCUpdate
                            (
                              NTP4VCUpdate
                                E
                                ( NTP4VCShift A D )
                                (
                                  E
                                  `
                                  ( NTP4VCShift A ( C - 1 ) )
                                )
                            )
                            ( NTP4VCShift A ( C - 1 ) )
                            ( B ` ( NTP4VCShift A 0 ) )
                        )
                        =
                        I
                        /\
                        (
                          0 < H
                          /\
                          (
                            0 <_ D
                            /\
                            (
                              D < F
                              /\
                              (
                                (
                                  E
                                  `
                                  ( NTP4VCShift A ( C - 1 ) )
                                )
                                <
                                (
                                  E
                                  `
                                  (
                                    NTP4VCShift
                                      A
                                      ( NTP4VCHeapParent D )
                                  )
                                )
                                /\
                                (
                                  ( 2 + D ) <_ C
                                  /\
                                  (
                                    ( NTP4VCIsHeap E A C )
                                    /\
                                    (
                                      (
                                        NTP4VCHeapMaximumChild
                                          E A C D F
                                      )
                                      /\
                                      (
                                        (
                                          NTP4VCHeapMaximumChild
                                            B A C 0 H
                                        )
                                        /\
                                        (
                                          (
                                            NTP4VCValidRW
                                              L
                                              ( NTP4VCShift A 0 )
                                              C
                                          )
                                          /\
                                          (
                                            (
                                              NTP4VCValidRW
                                                L
                                                ( NTP4VCShift A D )
                                                1
                                            )
                                            /\
                                            (
                                              (
                                                NTP4VCUpperBound
                                                  E
                                                  A
                                                  0
                                                  C
                                                  (
                                                    B
                                                    `
                                                    (
                                                      NTP4VCShift
                                                        A
                                                        0
                                                    )
                                                  )
                                              )
                                              /\
                                              (
                                                (
                                                  NTP4VCValidRD
                                                    L
                                                    (
                                                      NTP4VCShift
                                                        A
                                                        (
                                                          P
                                                          `
                                                          ( C - 1 )
                                                        )
                                                    )
                                                    1
                                                )
                                                /\
                                                (
                                                  (
                                                    NTP4VCValidRW
                                                      L
                                                      (
                                                        NTP4VCShift
                                                          A
                                                          (
                                                            P
                                                            `
                                                            ( C - 1 )
                                                          )
                                                      )
                                                      1
                                                  )
                                                  /\
                                                  (
                                                    (
                                                      ( 2 + H ) <_ C
                                                      ->
                                                      (
                                                        NTP4VCHeapParent
                                                          H
                                                      )
                                                      =
                                                      0
                                                    )
                                                    /\
                                                    (
                                                      (
                                                        ( 2 + F ) <_ C
                                                        ->
                                                        (
                                                          NTP4VCHeapParent
                                                            F
                                                        )
                                                        =
                                                        D
                                                      )
                                                      /\
                                                      (
                                                        (
                                                          C <_ ( 1 + F )
                                                          \/
                                                          (
                                                            (
                                                              E
                                                              `
                                                              (
                                                                NTP4VCShift
                                                                  A
                                                                  F
                                                              )
                                                            )
                                                            <_
                                                            (
                                                              E
                                                              `
                                                              (
                                                                NTP4VCShift
                                                                  A
                                                                  ( C - 1 )
                                                              )
                                                            )
                                                            /\
                                                            (
                                                              NTP4VCValidRD
                                                                L
                                                                (
                                                                  NTP4VCShift
                                                                    A
                                                                    F
                                                                )
                                                                1
                                                            )
                                                          )
                                                        )
                                                        /\
                                                        (
                                                          A. v e. ZZ
                                                            (
                                                              (
                                                                NTP4VCSint32 v
                                                              )
                                                              ->
                                                              (
                                                                (
                                                                  (
                                                                    NTP4VCCount
                                                                      Q B A 0 C v
                                                                  )
                                                                  +
                                                                  if (
                                                                    (
                                                                      E
                                                                      `
                                                                      (
                                                                        NTP4VCShift
                                                                          A
                                                                          D
                                                                      )
                                                                    )
                                                                    =
                                                                    v ,
                                                                    1 ,
                                                                    0
                                                                  )
                                                                )
                                                                =
                                                                (
                                                                  (
                                                                    NTP4VCCount
                                                                      Q E A 0 C v
                                                                  )
                                                                  +
                                                                  if (
                                                                    (
                                                                      B
                                                                      `
                                                                      (
                                                                        NTP4VCShift
                                                                          A
                                                                          0
                                                                      )
                                                                    )
                                                                    =
                                                                    v ,
                                                                    1 ,
                                                                    0
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
              -.
              (
                ( B ` ( NTP4VCShift A ( C - 1 ) ) )
                <
                ( B ` ( NTP4VCShift A 0 ) )
              )
              ->
              I = B
            )
          )
        )
      )
    )
    /\
    (
      -. 2 <_ C
      ->
      I = B
    )
  ) $.

  ntp4vc-pop-heap-post-result-goal1 $a |- (
    ( I ` ( NTP4VCShift A ( C - 1 ) ) )
    =
    ( B ` ( NTP4VCShift A 0 ) )
  ) $.
$}
