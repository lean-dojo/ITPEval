$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_post_Unique_goal8:
  distinct array indices still map to distinct linked-list node addresses
  after the array-pop havoc update, under the generated integer bounds,
  memory validity, framing, linkage, swipe, unchanged, distinctness, and
  separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, and NTP4VCValidRW expand the
  corresponding source definitions. NTP4VCHavoc is the source havoc function
  fixed pointwise by havoc_access.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  existentially quantified integer-indexed address function records the finite
  chain from the root at position zero to the bound at position n. At every
  integer position in the chain it preserves the array lookup, writable-node
  condition, and next-pointer step.

  NTP4VCSwipeLeft directly expands p_array_swipe_left. In both source
  p_unchanged assumptions the allocation map and real memory are identical on
  the two sides. NTP4VCUnchanged therefore keeps exactly the bidirectionally
  equivalent nontrivial fields: equality of each array pointer and equality of
  the corresponding next-pointer reads. Pointer equality supplies the source
  float-field equalities and writable implication, and the source conjunction
  supplies the two displayed equalities in the converse direction.

  The region function and linked predicate have no constraining source axioms,
  so they are represented by an arbitrary integer map and an arbitrary subset
  of integer maps. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no local $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCLinkedN NTP4VCSwipeLeft NTP4VCUnchanged
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-linked-n-syntax
  $a wff ( NTP4VCLinkedN A B C D P Q R ) $.
ntp4vc-swipe-left-syntax
  $a wff ( NTP4VCSwipeLeft A B C D P ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D P ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.
ntp4vc-sint-limit-def $a |- NTP4VCSintLimit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
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
        (
          ( ( NTP4VCOffset B ) + C )
          <_
          ( A ` ( NTP4VCBase B ) )
        )
      )
    )
  )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSintLimit <_ A /\ A < NTP4VCSintLimit )
) $.

${
  $d x A B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
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

${
  $d f x $.
  $d f A B C D P Q R $.
  $d x A B C D P Q R $.
  ntp4vc-linked-n-def $a |- ( ( NTP4VCLinkedN A B C D P Q R ) <->
    (
      P e. ZZ
      /\
      (
        Q e. ZZ
        /\
        (
          0 <_ P
          /\
          (
            0 <_ Q
            /\
            (
              ( P + Q ) <_ NTP4VCMaxIndex
              /\
              E. f e. ( NTP4VCAddr ^m ZZ )
              (
                ( f ` 0 ) = C
                /\
                (
                  ( f ` Q ) = R
                  /\
                  A. x e. ZZ
                  (
                    ( 0 <_ x /\ x < Q )
                    ->
                    (
                      ( B ` ( NTP4VCShift D ( P + x ) ) ) = ( f ` x )
                      /\
                      (
                        ( NTP4VCValidRW A ( f ` x ) 4 )
                        /\
                        (
                          ( f ` ( x + 1 ) )
                          =
                          ( B ` ( NTP4VCShift ( f ` x ) 0 ) )
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
  ) $.
$}

${
  $d x A B C D P $.
  ntp4vc-swipe-left-def $a |- ( ( NTP4VCSwipeLeft A B C D P ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x < P )
      ->
      (
        ( B ` ( NTP4VCShift C ( 1 + x ) ) )
        =
        ( A ` ( NTP4VCShift C x ) )
      )
    )
  ) $.
$}

${
  $d x A B C D P $.
  ntp4vc-unchanged-def $a |- ( ( NTP4VCUnchanged A B C D P ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x < P )
      ->
      (
        ( A ` ( NTP4VCShift C x ) )
        =
        ( B ` ( NTP4VCShift C x ) )
        /\
        (
          A
          `
          (
            NTP4VCShift
            ( A ` ( NTP4VCShift C x ) )
            0
          )
        )
        =
        (
          B
          `
          (
            NTP4VCShift
            ( B ` ( NTP4VCShift C x ) )
            0
          )
        )
      )
    )
  ) $.
$}

${
  $d A B C D E F G H I J K L M N O P Q $.
  $d x y A B C D E F G H I J K L M N O P Q $.

  $( Source parameters:
     A=t_2, B=t_3, C=a_4, D=i_2, E=i, F=a_1, G=i_5, H=i_1,
     I=i_4, J=i_3, K=a, L=a_3, M=t, N=a_2, O=t_1,
     P=region, Q=linked extension. $)

  ntp4vc-t2-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-t3-map $e |- B e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-array-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-a1-address $e |- F e. NTP4VCAddr $.
  ntp4vc-i5-integer $e |- G e. ZZ $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-i4-integer $e |- I e. ZZ $.
  ntp4vc-i3-integer $e |- J e. ZZ $.
  ntp4vc-a-address $e |- K e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- L e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-a2-address $e |- N e. NTP4VCAddr $.
  ntp4vc-real-memory $e |- O e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- P e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- Q C_ ( ZZ ^m ZZ ) $.

  ntp4vc-indices-distinct $e |- I =/= J $.

  ntp4vc-havoc-a1 $e |- (
    (
      ( NTP4VCHavoc
        A B
        ( NTP4VCShift C D )
        ( E - 1 )
      )
      `
      F
    )
    =
    ( B ` F )
  ) $.

  ntp4vc-i-positive $e |- 0 < E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ H $.
  ntp4vc-i1-le-i2 $e |- H <_ D $.
  ntp4vc-i1-le-i3 $e |- H <_ J $.
  ntp4vc-i1-le-i4 $e |- H <_ I $.
  ntp4vc-i2-le-i5 $e |- D <_ G $.
  ntp4vc-i5-lt-x $e |- G < ( E + D ) $.

  ntp4vc-region-a $e |- ( P ` ( NTP4VCBase K ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( P ` ( NTP4VCBase F ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( P ` ( NTP4VCBase L ) ) <_ 0 $.
  ntp4vc-region-a4 $e |- ( P ` ( NTP4VCBase C ) ) <_ 0 $.

  ntp4vc-i3-gap-bound $e |- ( 2 + J ) <_ ( E + D ) $.
  ntp4vc-i4-gap-bound $e |- ( 2 + I ) <_ ( E + D ) $.
  ntp4vc-x-le-x1 $e |- ( E + D ) <_ ( 1 + G ) $.

  ntp4vc-framed-t3 $e |- ( NTP4VCFramed P B ) $.
  ntp4vc-linked-allocation $e |- M e. Q $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i5-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW M ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a1-array-separated $e |- (
    NTP4VCSeparated F 1 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a6-array-separated $e |- (
    NTP4VCSeparated
      ( B ` F ) 4
      ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-main $e |- (
    NTP4VCLinkedN M B K C D E L
  ) $.

  ntp4vc-linked-prefix $e |- (
    NTP4VCLinkedN
      M B
      ( B ` ( NTP4VCShift C H ) )
      C H ( D - H ) K
  ) $.

  ntp4vc-array-swipe-left $e |- (
    NTP4VCSwipeLeft
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      B C D G
  ) $.

  ntp4vc-linked-after-upper $e |- (
    NTP4VCLinkedN
      M
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      N C
      ( 1 + G )
      ( ( ( E + D ) - 1 ) - G )
      L
  ) $.

  ntp4vc-linked-prefix-after-havoc $e |- (
    NTP4VCLinkedN
      M
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      ( B ` ( NTP4VCShift C H ) )
      C H ( D - H ) K
  ) $.

  ntp4vc-linked-center-after-havoc $e |- (
    NTP4VCLinkedN
      M
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      (
        (
          NTP4VCHavoc A B
          ( NTP4VCShift C D )
          ( E - 1 )
        )
        `
        ( NTP4VCShift K 0 )
      )
      C D ( G - D ) N
  ) $.

  ntp4vc-unchanged-lower $e |- (
    NTP4VCUnchanged
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      B C H D
  ) $.

  ntp4vc-unchanged-upper $e |- (
    NTP4VCUnchanged
      ( NTP4VCHavoc A B ( NTP4VCShift C D ) ( E - 1 ) )
      B C G ( E + D )
  ) $.

  ntp4vc-a1-node-separated $e |- A. x e. ZZ
    (
      ( H <_ x /\ x < ( E + D ) )
      ->
      (
        NTP4VCSeparated
          F 1
          ( B ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-node-array-separated $e |- A. x e. ZZ
    (
      ( H <_ x /\ x < ( E + D ) )
      ->
      (
        NTP4VCSeparated
          ( B ` ( NTP4VCShift C x ) ) 4
          ( NTP4VCShift C 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-node-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          H <_ x
          /\
          (
            H <_ y
            /\
            (
              x < ( E + D )
              /\
              y < ( E + D )
            )
          )
        )
      )
      ->
      (
        ( B ` ( NTP4VCShift C y ) )
        =/=
        ( B ` ( NTP4VCShift C x ) )
      )
    ) $.

  ntp4vc-node-pair-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          H <_ x
          /\
          (
            H <_ y
            /\
            (
              x < ( E + D )
              /\
              y < ( E + D )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( B ` ( NTP4VCShift C y ) ) 4
          ( B ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-array-pop-post-unique-goal8 $a |- (
    (
      (
        (
          NTP4VCHavoc A B
          ( NTP4VCShift C D )
          ( E - 1 )
        )
        `
        ( NTP4VCShift C I )
      )
    )
    =/=
    (
      (
        (
          NTP4VCHavoc A B
          ( NTP4VCShift C D )
          ( E - 1 )
        )
        `
        ( NTP4VCShift C J )
      )
    )
  ) $.
$}
