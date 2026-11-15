$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_Separation_2_part4_goal41:
  the list-push verification condition states that the distinct nodes
  selected at indices i_5 and i_4 are separated in the final pointer map
  after index search, memory havoc, and pointer-map updates, under the
  generated bounds, validity, framing, linkage, structure-equality,
  distinctness, and separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. The definitions below
  expand the source shift, separation, writable-validity, signed-32-bit,
  framing, functional-update, havoc, structure-load, swipe, and unchanged
  operations.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate,
  using an integer-indexed finite chain. NTP4VCIndexOfEq is the exact graph of
  l_index_of: it returns the first matching position in the half-open search
  interval, or the upper-bound sentinel. The source let-bound search result
  x_2 is represented by one integer variable constrained by this functional
  graph for both source occurrences. NTP4VCFound and NTP4VCNoFound retain the
  original existential and universal branch conditions over all integers.

  NTP4VCPreMap, NTP4VCPostMap, NTP4VCStageMap, and NTP4VCFinalMap name only
  the source let-bound maps a_11, a_16, a_13, and a_14. NTP4VCLoadS1 retains
  the pointer field and all three real fields. The arbitrary source region
  function and linked predicate are retained as an integer map and a subset
  of integer maps. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCUpdate NTP4VCPreMap NTP4VCPostMap NTP4VCStageMap
  NTP4VCFinalMap NTP4VCLoadS1
  NTP4VCLinkedN NTP4VCIndexOfEq NTP4VCSwipeLeft NTP4VCSwipeRight
  NTP4VCUnchanged
  NTP4VCFound NTP4VCNoFound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-pre-map-class
  $a class ( NTP4VCPreMap A B C D E F G H I ) $.
ntp4vc-post-map-class
  $a class ( NTP4VCPostMap A B C D E F G H I J ) $.
ntp4vc-stage-map-class
  $a class ( NTP4VCStageMap A B C D E F G H I J K ) $.
ntp4vc-final-map-class
  $a class ( NTP4VCFinalMap A B C D E F G H I J K ) $.
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
ntp4vc-index-of-eq-syntax
  $a wff ( NTP4VCIndexOfEq A B C D E F ) $.
ntp4vc-swipe-left-syntax
  $a wff ( NTP4VCSwipeLeft A B C D P ) $.
ntp4vc-swipe-right-syntax
  $a wff ( NTP4VCSwipeRight A B C D P ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E F G ) $.
ntp4vc-found-syntax
  $a wff ( NTP4VCFound A B C D E ) $.
ntp4vc-no-found-syntax
  $a wff ( NTP4VCNoFound A B C D E ) $.

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
        ( ( NTP4VCOffset B ) + C ) <_ ( A ` ( NTP4VCBase B ) )
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

ntp4vc-pre-map-def $a |- (
  NTP4VCPreMap A B C D E F G H I
) =
  (
    NTP4VCHavoc
      F
      (
        NTP4VCUpdate
          ( NTP4VCUpdate A G H )
          (
            NTP4VCShift
              ( A ` ( NTP4VCShift B ( C - 1 ) ) )
              0
          )
          I
      )
      ( NTP4VCShift B C )
      ( ( D + E ) - C )
  ) $.

ntp4vc-post-map-def $a |- (
  NTP4VCPostMap A B C D E F G H I J
) =
  (
    NTP4VCHavoc
      J
      ( NTP4VCPreMap A B C D E F G H I )
      ( NTP4VCShift B ( E - 1 ) )
      ( 1 + D )
  ) $.

ntp4vc-stage-map-def $a |- (
  NTP4VCStageMap A B C D E F G H I J K
) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          ( NTP4VCPostMap A B J D E F G H I K )
          ( NTP4VCShift ( A ` ( NTP4VCShift B C ) ) 0 )
          (
            (
              NTP4VCPreMap A B J D E F G H I
            )
            `
            G
          )
      )
      ( NTP4VCShift B ( E - 1 ) )
      ( A ` ( NTP4VCShift B C ) )
  ) $.

ntp4vc-final-map-def $a |- (
  NTP4VCFinalMap A B C D E F G H I J K
) =
  (
    NTP4VCUpdate
      ( NTP4VCStageMap A B C D E F G H I J K )
      G
      ( A ` ( NTP4VCShift B C ) )
  ) $.

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
  $d x A B C D P $.
  ntp4vc-swipe-right-def $a |- ( ( NTP4VCSwipeRight A B C D P ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x < P )
      ->
      (
        ( B ` ( NTP4VCShift C ( x - 1 ) ) )
        =
        ( A ` ( NTP4VCShift C x ) )
      )
    )
  ) $.
$}

${
  $d x A B C D E F G $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D E F G )
    <->
    A. x e. ZZ
    (
      ( F <_ x /\ x < G )
      ->
      (
        ( B ` ( NTP4VCShift E x ) )
        =
        ( D ` ( NTP4VCShift E x ) )
        /\
        (
          (
            NTP4VCLoadS1
              ( D ` ( NTP4VCShift E x ) )
              C D
          )
          =
          (
            NTP4VCLoadS1
              ( B ` ( NTP4VCShift E x ) )
              C B
          )
          /\
          (
            (
              NTP4VCValidRW
                A
                ( D ` ( NTP4VCShift E x ) )
                4
            )
            ->
            (
              NTP4VCValidRW
                A
                ( B ` ( NTP4VCShift E x ) )
                4
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-found-def $a |- ( ( NTP4VCFound A B C D E ) <->
    E. x e. ZZ
    (
      B = ( A ` ( NTP4VCShift C x ) )
      /\
      ( x < E /\ D <_ ( 1 + x ) )
    )
  ) $.

  ntp4vc-no-found-def $a |- ( ( NTP4VCNoFound A B C D E ) <->
    A. x e. ZZ
    (
      x < E
      ->
      (
        D <_ ( 1 + x )
        ->
        B =/= ( A ` ( NTP4VCShift C x ) )
      )
    )
  ) $.
$}

${
  $d A B C D E F G H I J K L M N O P Q R $.
  $d x y A B C D E F G H I J K L M N O P Q R $.

  $( Source parameters:
     A=t_3, B=a_3, C=i_3, D=i_2, E=i_1, F=i, G=a_2,
     H=t_2, I=a, J=a_1, K=t, L=t_1, M=region,
     N=linked predicate, O=x_2, P=i_4, Q=i_5, and R=t_4. $)

  ntp4vc-t3-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i3-integer $e |- C e. ZZ $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-a2-address $e |- G e. NTP4VCAddr $.
  ntp4vc-t2-map $e |- H e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- I e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- J e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory $e |- L e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- N C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-a4-integer $e |- O e. ZZ $.
  ntp4vc-i4-integer $e |- P e. ZZ $.
  ntp4vc-i5-integer $e |- Q e. ZZ $.
  ntp4vc-t4-map $e |- R e. ( NTP4VCAddr ^m NTP4VCAddr ) $.

  ntp4vc-i5-not-i4 $e |- Q =/= P $.

  ntp4vc-a4-not-null $e |- (
    ( A ` ( NTP4VCShift B C ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a4-equals-a5 $e |- (
    ( A ` ( NTP4VCShift B C ) )
    =
    ( A ` ( NTP4VCShift B D ) )
  ) $.

  ntp4vc-index-a4-result $e |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift B C ) )
      B
      ( E - 1 )
      ( F + E )
      O
  ) $.

  ntp4vc-index-a5-result $e |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift B D ) )
      B
      ( E - 1 )
      ( F + E )
      O
  ) $.

  ntp4vc-index-before-upper $e |- ( F + E ) =/= O $.
  ntp4vc-i1-positive $e |- 0 < E $.
  ntp4vc-i2-before-upper $e |- D < ( F + E ) $.
  ntp4vc-i3-before-upper $e |- C < ( F + E ) $.
  ntp4vc-i4-before-upper $e |- P < ( F + E ) $.
  ntp4vc-i5-before-upper $e |- Q < ( F + E ) $.

  ntp4vc-region-a2 $e |- (
    ( M ` ( NTP4VCBase G ) ) <_ 0
  ) $.

  ntp4vc-region-a3 $e |- (
    ( M ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a4 $e |- (
    ( M ` ( NTP4VCBase ( A ` ( NTP4VCShift B C ) ) ) ) <_ 0
  ) $.

  ntp4vc-index-strict-upper $e |- O < ( F + E ) $.
  ntp4vc-index-upper $e |- O <_ ( F + E ) $.
  ntp4vc-i-lower-bound $e |- -u 1 <_ F $.
  ntp4vc-i-upper-bound $e |- F <_ ( NTP4VCMaxIndex - 2 ) $.
  ntp4vc-upper-bound $e |- ( F + E ) <_ ( NTP4VCMaxIndex - 1 ) $.
  ntp4vc-i1-le-i2-plus-one $e |- E <_ ( 1 + D ) $.
  ntp4vc-i1-le-i3-plus-one $e |- E <_ ( 1 + C ) $.
  ntp4vc-i1-le-i4-plus-one $e |- E <_ ( 1 + P ) $.
  ntp4vc-i1-le-i5-plus-one $e |- E <_ ( 1 + Q ) $.
  ntp4vc-i1-le-index-plus-one $e |- E <_ ( 1 + O ) $.

  ntp4vc-framed-t3 $e |- ( NTP4VCFramed M A ) $.
  ntp4vc-linked-allocation $e |- K e. N $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-a2-valid $e |- ( NTP4VCValidRW K G 1 ) $.
  ntp4vc-search-lower-sint32 $e |- ( NTP4VCSint32 ( E - 1 ) ) $.
  ntp4vc-i-plus-one-sint32 $e |- ( NTP4VCSint32 ( 1 + F ) ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      K
      ( NTP4VCShift B 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a5-valid $e |- (
    NTP4VCValidRW
      K
      ( A ` ( NTP4VCShift B D ) )
      4
  ) $.

  ntp4vc-a2-array-separated $e |- (
    NTP4VCSeparated
      G 1
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-t3-a2-array-separated $e |- (
    NTP4VCSeparated
      ( A ` G ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a2-a5-separated $e |- (
    NTP4VCSeparated
      G 1
      ( A ` ( NTP4VCShift B D ) ) 4
  ) $.

  ntp4vc-a5-array-separated $e |- (
    NTP4VCSeparated
      ( A ` ( NTP4VCShift B D ) ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-search-suffix-valid $e |- (
    NTP4VCValidRW
      K
      ( NTP4VCShift B ( E - 1 ) )
      ( 1 + F )
  ) $.

  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN
      K A ( A ` G ) B
      ( E - 1 ) ( 1 + F ) <. 0 , 0 >.
  ) $.

  ntp4vc-index-a4-sint32 $e |- ( NTP4VCSint32 O ) $.

  ntp4vc-premap-a2-array-separated $e |- (
    NTP4VCSeparated
      (
        (
          NTP4VCPreMap A B O F E H G I J
        )
        `
        G
      )
      4
      ( NTP4VCShift B 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a4-structure-equal $e |- (
    (
      NTP4VCLoadS1
        ( A ` ( NTP4VCShift B C ) )
        L
        ( NTP4VCPreMap A B O F E H G I J )
    )
    =
    (
      NTP4VCLoadS1
        ( A ` ( NTP4VCShift B C ) )
        L A
    )
  ) $.

  ntp4vc-stage-unchanged $e |- (
    NTP4VCUnchanged
      K
      ( NTP4VCFinalMap A B C F E H G I J O R )
      L
      ( NTP4VCStageMap A B C F E H G I J O R )
      B
      ( E - 1 )
      ( F + E )
  ) $.

  ntp4vc-found-link $e |- (
    E <_ O
    ->
    (
      (
        NTP4VCFound
          A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
      )
      ->
      (
        (
          NTP4VCPreMap A B O F E H G I J
        )
        `
        ( NTP4VCShift B ( O - 1 ) )
      )
      =
      ( A ` ( NTP4VCShift B ( O - 1 ) ) )
    )
  ) $.

  ntp4vc-found-swipe-left $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    (
      NTP4VCSwipeLeft
        ( NTP4VCPreMap A B O F E H G I J )
        A B O ( ( F + E ) - 1 )
    )
  ) $.

  ntp4vc-not-found-no-a4-premap $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          (
            NTP4VCPreMap A B O F E H G I J
          )
          `
          ( NTP4VCShift B x )
        )
        =/=
        ( A ` ( NTP4VCShift B C ) )
      )
    )
  ) $.

  ntp4vc-found-no-a4-premap $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      E <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( F + E )
        ->
        (
          (
            NTP4VCPreMap A B O F E H G I J
          )
          `
          ( NTP4VCShift B x )
        )
        =/=
        ( A ` ( NTP4VCShift B C ) )
      )
    )
  ) $.

  ntp4vc-found-linked-premap $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    (
      NTP4VCLinkedN
        K
        ( NTP4VCPreMap A B O F E H G I J )
        (
          (
            NTP4VCPreMap A B O F E H G I J
          )
          `
          G
        )
        B
        ( E - 1 )
        F
        <. 0 , 0 >.
    )
  ) $.

  ntp4vc-not-found-linked-premap $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    (
      NTP4VCLinkedN
        K
        ( NTP4VCPreMap A B O F E H G I J )
        (
          (
            NTP4VCPreMap A B O F E H G I J
          )
          `
          G
        )
        B
        ( E - 1 )
        ( 1 + F )
        <. 0 , 0 >.
    )
  ) $.

  ntp4vc-not-found-unchanged $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    (
      NTP4VCUnchanged
        K
        ( NTP4VCPreMap A B O F E H G I J )
        L A B
        ( E - 1 )
        ( F + E )
    )
  ) $.

  ntp4vc-found-unchanged $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    (
      NTP4VCUnchanged
        K
        ( NTP4VCPreMap A B O F E H G I J )
        L A B
        ( E - 1 )
        ( O - 1 )
    )
  ) $.

  ntp4vc-not-found-a2-premap-separated $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            G 1
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-a2-premap-separated $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      E <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( F + E )
        ->
        (
          NTP4VCSeparated
            G 1
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-a4-premap-separated $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            ( A ` ( NTP4VCShift B C ) ) 4
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-a4-premap-separated $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      E <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( F + E )
        ->
        (
          NTP4VCSeparated
            ( A ` ( NTP4VCShift B C ) ) 4
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-premap-array-separated $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
            ( NTP4VCShift B 0 )
            NTP4VCMaxIndex
        )
      )
    )
  ) $.

  ntp4vc-found-premap-array-separated $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      E <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( F + E )
        ->
        (
          NTP4VCSeparated
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            4
            ( NTP4VCShift B 0 )
            NTP4VCMaxIndex
        )
      )
    )
  ) $.

  ntp4vc-found-load-equality $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. x e. ZZ
    (
      O <_ x
      ->
      (
        ( 2 + x ) <_ ( F + E )
        ->
        (
          NTP4VCLoadS1
            (
              (
                NTP4VCPreMap A B O F E H G I J
              )
              `
              ( NTP4VCShift B x )
            )
            L
            ( NTP4VCPreMap A B O F E H G I J )
        )
        =
        (
          NTP4VCLoadS1
            ( A ` ( NTP4VCShift B ( 1 + x ) ) )
            L A
        )
      )
    )
  ) $.

  ntp4vc-not-found-premap-distinct $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( F + E )
        ->
        (
          y < ( F + E )
          ->
          (
            E <_ ( 1 + x )
            ->
            (
              E <_ ( 1 + y )
              ->
              (
                (
                  NTP4VCPreMap A B O F E H G I J
                )
                `
                ( NTP4VCShift B y )
              )
              =/=
              (
                (
                  NTP4VCPreMap A B O F E H G I J
                )
                `
                ( NTP4VCShift B x )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-premap-distinct $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          E <_ ( 1 + y )
          ->
          (
            ( 2 + x ) <_ ( F + E )
            ->
            (
              ( 2 + y ) <_ ( F + E )
              ->
              (
                (
                  NTP4VCPreMap A B O F E H G I J
                )
                `
                ( NTP4VCShift B y )
              )
              =/=
              (
                (
                  NTP4VCPreMap A B O F E H G I J
                )
                `
                ( NTP4VCShift B x )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-not-found-premap-pair-separated $e |- (
    (
      NTP4VCNoFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( F + E )
        ->
        (
          y < ( F + E )
          ->
          (
            E <_ ( 1 + x )
            ->
            (
              E <_ ( 1 + y )
              ->
              (
                NTP4VCSeparated
                  (
                    (
                      NTP4VCPreMap A B O F E H G I J
                    )
                    `
                    ( NTP4VCShift B y )
                  )
                  4
                  (
                    (
                      NTP4VCPreMap A B O F E H G I J
                    )
                    `
                    ( NTP4VCShift B x )
                  )
                  4
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-premap-pair-separated $e |- (
    (
      NTP4VCFound
        A ( A ` ( NTP4VCShift B C ) ) B E ( F + E )
    )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          E <_ ( 1 + y )
          ->
          (
            ( 2 + x ) <_ ( F + E )
            ->
            (
              ( 2 + y ) <_ ( F + E )
              ->
              (
                NTP4VCSeparated
                  (
                    (
                      NTP4VCPreMap A B O F E H G I J
                    )
                    `
                    ( NTP4VCShift B y )
                  )
                  4
                  (
                    (
                      NTP4VCPreMap A B O F E H G I J
                    )
                    `
                    ( NTP4VCShift B x )
                  )
                  4
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a2-nodes-separated $e |- A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            G 1
            ( A ` ( NTP4VCShift B x ) ) 4
        )
      )
    ) $.

  ntp4vc-nodes-array-separated $e |- A. x e. ZZ
    (
      x < ( F + E )
      ->
      (
        E <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            ( A ` ( NTP4VCShift B x ) ) 4
            ( NTP4VCShift B 0 ) NTP4VCMaxIndex
        )
      )
    ) $.

  ntp4vc-a5-nodes-separated $e |- A. x e. ZZ
    (
      ( A ` ( NTP4VCShift B D ) )
      =/=
      ( A ` ( NTP4VCShift B x ) )
      ->
      (
        x < ( F + E )
        ->
        (
          E <_ ( 1 + x )
          ->
          (
            NTP4VCSeparated
              ( A ` ( NTP4VCShift B D ) ) 4
              ( A ` ( NTP4VCShift B x ) ) 4
          )
        )
      )
    ) $.

  ntp4vc-a4-nodes-separated $e |- A. x e. ZZ
    (
      ( A ` ( NTP4VCShift B C ) )
      =/=
      ( A ` ( NTP4VCShift B x ) )
      ->
      (
        x < ( F + E )
        ->
        (
          E <_ ( 1 + x )
          ->
          (
            NTP4VCSeparated
              ( A ` ( NTP4VCShift B C ) ) 4
              ( A ` ( NTP4VCShift B x ) ) 4
          )
        )
      )
    ) $.

  ntp4vc-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( F + E )
        ->
        (
          y < ( F + E )
          ->
          (
            E <_ ( 1 + x )
            ->
            (
              E <_ ( 1 + y )
              ->
              (
                ( A ` ( NTP4VCShift B y ) )
                =/=
                ( A ` ( NTP4VCShift B x ) )
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-nodes-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( F + E )
        ->
        (
          y < ( F + E )
          ->
          (
            E <_ ( 1 + x )
            ->
            (
              E <_ ( 1 + y )
              ->
              (
                NTP4VCSeparated
                  ( A ` ( NTP4VCShift B y ) ) 4
                  ( A ` ( NTP4VCShift B x ) ) 4
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-postmap-a2 $e |- (
    (
      (
        NTP4VCPostMap A B O F E H G I J R
      )
      `
      G
    )
    =
    (
      (
        NTP4VCPreMap A B O F E H G I J
      )
      `
      G
    )
  ) $.

  ntp4vc-postmap-a2-array-separated $e |- (
    NTP4VCSeparated
      (
        (
          NTP4VCPostMap A B O F E H G I J R
        )
        `
        G
      )
      4
      ( NTP4VCShift B 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a2-postmap-nodes-separated $e |- A. x e. ZZ
    (
      E <_ x
      ->
      (
        x < ( F + E )
        ->
        (
          NTP4VCSeparated
            G 1
            (
              (
                NTP4VCPostMap A B O F E H G I J R
              )
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    ) $.

  ntp4vc-postmap-nodes-array-separated $e |- A. x e. ZZ
    (
      E <_ x
      ->
      (
        x < ( F + E )
        ->
        (
          NTP4VCSeparated
            (
              (
                NTP4VCPostMap A B O F E H G I J R
              )
              `
              ( NTP4VCShift B x )
            )
            4
            ( NTP4VCShift B 0 )
            NTP4VCMaxIndex
        )
      )
    ) $.

  ntp4vc-postmap-nodes-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        E <_ x
        ->
        (
          E <_ y
          ->
          (
            x < ( F + E )
            ->
            (
              y < ( F + E )
              ->
              (
                NTP4VCSeparated
                  (
                    (
                      NTP4VCPostMap A B O F E H G I J R
                    )
                    `
                    ( NTP4VCShift B y )
                  )
                  4
                  (
                    (
                      NTP4VCPostMap A B O F E H G I J R
                    )
                    `
                    ( NTP4VCShift B x )
                  )
                  4
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-postmap-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        ( E - 1 ) <_ x
        ->
        (
          ( E - 1 ) <_ y
          ->
          (
            x < ( F + E )
            ->
            (
              y < ( F + E )
              ->
              (
                (
                  (
                    NTP4VCPostMap A B O F E H G I J R
                  )
                  `
                  ( NTP4VCShift B y )
                )
                =/=
                (
                  (
                    NTP4VCPostMap A B O F E H G I J R
                  )
                  `
                  ( NTP4VCShift B x )
                )
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-postmap-swipe-right $e |- (
    NTP4VCSwipeRight
      ( NTP4VCPostMap A B O F E H G I J R )
      ( NTP4VCPreMap A B O F E H G I J )
      B E ( F + E )
  ) $.

  ntp4vc-postmap-linked $e |- (
    NTP4VCLinkedN
      K
      ( NTP4VCPostMap A B O F E H G I J R )
      (
        (
          NTP4VCPreMap A B O F E H G I J
        )
        `
        G
      )
      B E F <. 0 , 0 >.
  ) $.

  ntp4vc-list-push-contains-item-post-separation-2-part4-goal41 $a |- (
    NTP4VCSeparated
      (
        (
          NTP4VCFinalMap A B C F E H G I J O R
        )
        `
        ( NTP4VCShift B Q )
      )
      4
      (
        (
          NTP4VCFinalMap A B C F E H G I J O R
        )
        `
        ( NTP4VCShift B P )
      )
      4
  ) $.
$}
