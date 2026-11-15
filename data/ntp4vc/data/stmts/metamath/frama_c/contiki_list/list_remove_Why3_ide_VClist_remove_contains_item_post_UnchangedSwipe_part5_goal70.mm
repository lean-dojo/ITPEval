$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part5_goal70:
  the list-removal verification condition states that the updated pointer map
  preserves the four-field list structure at array position i4 by matching it
  with the successor structure in the original map, under the generated
  integer bounds, memory validity, framing, linkage, linked-segment,
  unchanged-state, index-search, distinctness, and separation assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCFramed, and NTP4VCUpdate directly expand the
  corresponding source definitions. NTP4VCLoadS1 retains the pointer field
  and all three real fields of load_s1_list.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  existentially quantified integer-indexed address function records the finite
  chain from the root at position zero to the bound at position n. At every
  integer position in the chain it preserves the array lookup, writable-node
  condition, and next-pointer step, together with the source index and length
  bounds. NTP4VCUnchanged expands the instantiated p_unchanged condition;
  both source states use the same allocation, pointer, and real-memory maps,
  so its field equalities and validity implication are retained reflexively.

  NTP4VCIndexOfEq is the total, single-valued graph of l_index_of: it returns
  the first matching integer position in the searched half-open interval, or
  the upper-bound sentinel if no position matches. P is constrained by this
  graph and names exactly the source let-bound index-search result. Every
  other source let-bound value is expanded at each use, and every source
  integer quantifier ranges over all of ZZ. NTP4VCHavoc,
  NTP4VCSwipeLeft, and NTP4VCUpdate directly encode the source post-havoc
  map, swipe relation, and full-domain functional update. The arbitrary
  source region function and linked predicate are retained as an integer map
  and a subset of integer maps. The final declaration is Metamath's native
  unproved $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCUpdate NTP4VCLoadS1 NTP4VCLinkedN
  NTP4VCUnchanged NTP4VCIndexOfEq NTP4VCSwipeLeft
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-load-s1-class $a class ( NTP4VCLoadS1 A B C ) $.

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
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D P Q ) $.
ntp4vc-index-of-eq-syntax
  $a wff ( NTP4VCIndexOfEq A B C D E F ) $.
ntp4vc-swipe-left-syntax
  $a wff ( NTP4VCSwipeLeft A B C D P ) $.

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
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

ntp4vc-load-s1-def $a |- ( NTP4VCLoadS1 A B C ) =
  <.
    ( C ` ( NTP4VCShift A 0 ) )
    ,
    <.
      ( B ` ( NTP4VCShift A 1 ) )
      ,
      <.
        ( B ` ( NTP4VCShift A 2 ) )
        ,
        ( B ` ( NTP4VCShift A 3 ) )
      >.
    >.
  >. $.

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
  $d x A B C D P Q $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D P Q )
    <->
    A. x e. ZZ
    (
      ( P <_ x /\ x < Q )
      ->
      (
        ( B ` ( NTP4VCShift D x ) )
        =
        ( B ` ( NTP4VCShift D x ) )
        /\
        (
          (
            B
            `
            (
              NTP4VCShift
              ( B ` ( NTP4VCShift D x ) )
              0
            )
          )
          =
          (
            B
            `
            (
              NTP4VCShift
              ( B ` ( NTP4VCShift D x ) )
              0
            )
          )
          /\
          (
            (
              C
              `
              (
                NTP4VCShift
                ( B ` ( NTP4VCShift D x ) )
                1
              )
            )
            =
            (
              C
              `
              (
                NTP4VCShift
                ( B ` ( NTP4VCShift D x ) )
                1
              )
            )
            /\
            (
              (
                C
                `
                (
                  NTP4VCShift
                  ( B ` ( NTP4VCShift D x ) )
                  2
                )
              )
              =
              (
                C
                `
                (
                  NTP4VCShift
                  ( B ` ( NTP4VCShift D x ) )
                  2
                )
              )
              /\
              (
                (
                  C
                  `
                  (
                    NTP4VCShift
                    ( B ` ( NTP4VCShift D x ) )
                    3
                  )
                )
                =
                (
                  C
                  `
                  (
                    NTP4VCShift
                    ( B ` ( NTP4VCShift D x ) )
                    3
                  )
                )
                /\
                (
                  ( NTP4VCValidRW A ( B ` ( NTP4VCShift D x ) ) 4 )
                  ->
                  ( NTP4VCValidRW A ( B ` ( NTP4VCShift D x ) ) 4 )
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
  $d x A B C D E F $.
  ntp4vc-index-of-eq-def $a |- (
    ( NTP4VCIndexOfEq A B C D E F )
    <->
    (
      ( E <_ D /\ F = E )
      \/
      (
        D < E
        /\
        (
          (
            F = E
            /\
            A. x e. ZZ
            (
              ( D <_ x /\ x < E )
              ->
              ( A ` ( NTP4VCShift C x ) ) =/= B
            )
          )
          \/
          (
            D <_ F
            /\
            (
              F < E
              /\
              (
                ( A ` ( NTP4VCShift C F ) ) = B
                /\
                A. x e. ZZ
                (
                  ( D <_ x /\ x < F )
                  ->
                  ( A ` ( NTP4VCShift C x ) ) =/= B
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
  $d A B C D E F G H I J K L M N O P $.
  $d x y A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_2, B=a_1, C=a, D=a_2, E=i_2, F=i, G=i_1, H=i_3,
     I=i_4, J=t, K=t_1, L=region, M=linked extension, N=t_3,
     O=t_4, and P=l_index_of result. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-post-havoc-map $e |- N e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-havoc-old-map $e |- O e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-i3-integer $e |- H e. ZZ $.
  ntp4vc-i4-integer $e |- I e. ZZ $.
  ntp4vc-allocation-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory-map $e |- K e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- M C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-result-integer $e |- P e. ZZ $.

  ntp4vc-a3-nonnull $e |- (
    ( A ` B ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a5-not-a3 $e |- (
    ( A ` ( NTP4VCShift C 0 ) ) =/= ( A ` B )
  ) $.

  ntp4vc-a6-nonnull $e |- (
    ( A ` ( NTP4VCShift D E ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a6-equals-a5 $e |- (
    ( A ` ( NTP4VCShift D E ) )
    =
    ( A ` ( NTP4VCShift C 0 ) )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-nonnegative $e |- 0 <_ G $.
  ntp4vc-i1-le-i2 $e |- G <_ E $.
  ntp4vc-i1-le-i3 $e |- G <_ H $.
  ntp4vc-i2-lt-x $e |- E < ( F + G ) $.
  ntp4vc-i3-le-x $e |- H <_ ( F + G ) $.

  ntp4vc-region-a1 $e |- (
    ( L ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a2 $e |- (
    ( L ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-region-a5 $e |- (
    ( L ` ( NTP4VCBase ( A ` ( NTP4VCShift C 0 ) ) ) ) <_ 0
  ) $.

  ntp4vc-index-le-i4 $e |- P <_ I $.

  ntp4vc-i-upper-bound $e |- (
    F <_ ( NTP4VCMaxIndex - 1 )
  ) $.

  ntp4vc-i4-room-for-successor $e |- (
    ( 2 + I ) <_ ( F + G )
  ) $.

  ntp4vc-framed-pointer-map $e |- (
    NTP4VCFramed L A
  ) $.

  ntp4vc-linked-allocation $e |- J e. M $.

  ntp4vc-i-sint32 $e |- (
    NTP4VCSint32 F
  ) $.

  ntp4vc-i1-sint32 $e |- (
    NTP4VCSint32 G
  ) $.

  ntp4vc-i3-sint32 $e |- (
    NTP4VCSint32 H
  ) $.

  ntp4vc-a1-valid $e |- (
    NTP4VCValidRW J B 1
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      J
      ( NTP4VCShift D 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a1-array-separated $e |- (
    NTP4VCSeparated
      B 1
      ( NTP4VCShift D 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a3-array-separated $e |- (
    NTP4VCSeparated
      ( A ` B ) 4
      ( NTP4VCShift D 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN
      J A ( A ` B ) D G F <. 0 , 0 >.
  ) $.

  ntp4vc-unchanged $e |- (
    NTP4VCUnchanged J A K D G H
  ) $.

  ntp4vc-single-node-linked $e |- (
    NTP4VCLinkedN
      J A C D H 1 ( A ` ( NTP4VCShift C 0 ) )
  ) $.

  ntp4vc-index-of-graph $e |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift D E ) )
      D G ( F + G ) P
  ) $.

  ntp4vc-index-sint32 $e |- (
    NTP4VCSint32 P
  ) $.

  ntp4vc-prefix-linked $e |- (
    NTP4VCLinkedN
      J A ( A ` B ) D G ( H - G ) C
  ) $.

  ntp4vc-suffix-linked $e |- (
    NTP4VCLinkedN
      J A
      ( A ` ( NTP4VCShift C 0 ) )
      D
      ( 1 + H )
      ( ( ( F + G ) - 1 ) - H )
      <. 0 , 0 >.
  ) $.

  ntp4vc-item-not-in-prefix $e |- A. x e. ZZ
    (
      ( G <_ x /\ x <_ H )
      ->
      (
        ( A ` ( NTP4VCShift D x ) )
        =/=
        ( A ` ( NTP4VCShift C 0 ) )
      )
    ) $.

  ntp4vc-a1-nodes-separated $e |- A. x e. ZZ
    (
      ( G <_ x /\ x < ( F + G ) )
      ->
      (
        NTP4VCSeparated
          B 1
          ( A ` ( NTP4VCShift D x ) ) 4
      )
    ) $.

  ntp4vc-a5-prefix-nodes-separated $e |- A. x e. ZZ
    (
      ( G <_ x /\ x < H )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C 0 ) ) 4
          ( A ` ( NTP4VCShift D x ) ) 4
      )
    ) $.

  ntp4vc-nodes-array-separated $e |- A. x e. ZZ
    (
      ( G <_ x /\ x < ( F + G ) )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift D x ) ) 4
          ( NTP4VCShift D 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-a6-other-node-separated $e |- A. x e. ZZ
    (
      (
        ( A ` ( NTP4VCShift D E ) )
        =/=
        ( A ` ( NTP4VCShift D x ) )
        /\
        ( G <_ x /\ x < ( F + G ) )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift D E ) ) 4
          ( A ` ( NTP4VCShift D x ) ) 4
      )
    ) $.

  ntp4vc-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          G <_ x
          /\
          (
            G <_ y
            /\
            (
              x < ( F + G )
              /\
              y < ( F + G )
            )
          )
        )
      )
      ->
      (
        ( A ` ( NTP4VCShift D y ) )
        =/=
        ( A ` ( NTP4VCShift D x ) )
      )
    ) $.

  ntp4vc-node-pairs-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          G <_ x
          /\
          (
            G <_ y
            /\
            (
              x < ( F + G )
              /\
              y < ( F + G )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift D y ) ) 4
          ( A ` ( NTP4VCShift D x ) ) 4
      )
    ) $.

  ntp4vc-havoc-state $e |- (
    (
      NTP4VCHavoc
        O A
        ( NTP4VCShift D ( 1 + H ) )
        ( ( ( F + G ) - 2 ) - H )
    )
    =
    N
  ) $.

  ntp4vc-swipe-before-update $e |- (
    NTP4VCSwipeLeft
      N A D ( 1 + H ) ( ( F + G ) - 1 )
  ) $.

  ntp4vc-post-nodes-array-separated $e |- A. x e. ZZ
    (
      ( G <_ x /\ x < ( ( F + G ) - 1 ) )
      ->
      (
        NTP4VCSeparated
          ( N ` ( NTP4VCShift D x ) ) 4
          ( NTP4VCShift D 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-post-node-pairs-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          G <_ x
          /\
          (
            G <_ y
            /\
            (
              x < ( ( F + G ) - 1 )
              /\
              y < ( ( F + G ) - 1 )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( N ` ( NTP4VCShift D y ) ) 4
          ( N ` ( NTP4VCShift D x ) ) 4
      )
    ) $.

  ntp4vc-list-remove-contains-item-post-unchanged-swipe-part5-goal70
    $a |- (
      (
        NTP4VCLoadS1
          (
            (
              NTP4VCUpdate
                N
                ( NTP4VCShift C 0 )
                (
                  A
                  `
                  (
                    NTP4VCShift
                      ( A ` ( NTP4VCShift C 0 ) )
                      0
                  )
                )
            )
            `
            ( NTP4VCShift D I )
          )
          K
          (
            NTP4VCUpdate
              N
              ( NTP4VCShift C 0 )
              (
                A
                `
                (
                  NTP4VCShift
                    ( A ` ( NTP4VCShift C 0 ) )
                    0
                )
              )
          )
      )
      =
      (
        NTP4VCLoadS1
          ( A ` ( NTP4VCShift D ( 1 + I ) ) )
          K A
      )
    ) $.
$}
