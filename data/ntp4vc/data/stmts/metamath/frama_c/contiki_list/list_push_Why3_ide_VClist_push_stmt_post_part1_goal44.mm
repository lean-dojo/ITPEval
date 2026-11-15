$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_push_Why3_ide_VClist_push_stmt_post_part1_goal44:
  the list-push verification condition establishes preservation of the
  array-backed linked-list region after index search, pointer-map updates,
  and two memory havocs, under the generated integer bounds, validity, linkage,
  separation, distinctness, swipe, and unchanged-region assumptions. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. The definitions below
  expand the source shift, separation, writable-validity, signed-32-bit,
  framing, functional-update, havoc, structure-load, left- and right-swipe,
  and unchanged operations.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate,
  using an integer-indexed finite chain. NTP4VCIndexOfEq is the exact graph of
  l_index_of: it returns the first matching position in the half-open search
  interval, or the upper-bound sentinel. The source let-bound search result
  x_2 is represented by one integer variable constrained by that graph.
  NTP4VCFound and NTP4VCNoFound retain the source existential and universal
  branch conditions over all integers.

  NTP4VCM, NTP4VCPreMap, NTP4VCA14, NTP4VCStageMap, and NTP4VCFinalMap name
  only the source let-bound maps m, a_11, a_14, a_12, and the concluding
  update of a_12. NTP4VCLoadS1 retains the pointer field and all three real
  fields. The arbitrary source region function and linked predicate are
  retained as an integer map and a subset of integer maps. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCUpdate NTP4VCM NTP4VCPreMap NTP4VCA14
  NTP4VCStageMap NTP4VCFinalMap NTP4VCLoadS1
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
ntp4vc-m-class $a class ( NTP4VCM A B C D E F G ) $.
ntp4vc-pre-map-class
  $a class ( NTP4VCPreMap A B C D E F G H ) $.
ntp4vc-a14-class
  $a class ( NTP4VCA14 A B C D E F G H I J ) $.
ntp4vc-stage-map-class
  $a class ( NTP4VCStageMap A B C D E F G H I J ) $.
ntp4vc-final-map-class
  $a class ( NTP4VCFinalMap A B C D E F G H I J ) $.
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
  $a wff ( NTP4VCSwipeLeft A B C D E ) $.
ntp4vc-swipe-right-syntax
  $a wff ( NTP4VCSwipeRight A B C D E ) $.
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

ntp4vc-m-def $a |- (
  NTP4VCM A B C D E F G
) =
  (
    NTP4VCUpdate
      ( NTP4VCUpdate A C D )
      (
        NTP4VCShift
          ( A ` ( NTP4VCShift B ( ( F + G ) - 2 ) ) )
          0
      )
      E
  ) $.

ntp4vc-pre-map-def $a |- (
  NTP4VCPreMap A B C D E F G H
) =
  (
    NTP4VCHavoc
      D
      ( NTP4VCM A B C E F G H )
      ( NTP4VCShift B ( ( G + H ) - 1 ) )
      0
  ) $.

ntp4vc-a14-def $a |- (
  NTP4VCA14 A B C D E F G H I J
) =
  (
    NTP4VCHavoc
      J
      ( NTP4VCPreMap A C D E F G H I )
      ( NTP4VCShift C ( I - 1 ) )
      ( 1 + H )
  ) $.

ntp4vc-stage-map-def $a |- (
  NTP4VCStageMap A B C D E F G H I J
) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          ( NTP4VCA14 A B C D E F G H I J )
          ( NTP4VCShift B 0 )
          ( ( NTP4VCPreMap A C D E F G H I ) ` D )
      )
      ( NTP4VCShift C ( I - 1 ) )
      B
  ) $.

ntp4vc-final-map-def $a |- (
  NTP4VCFinalMap A B C D E F G H I J
) =
  (
    NTP4VCUpdate
      ( NTP4VCStageMap A B C D E F G H I J )
      D
      B
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
  $d x A B C D E $.
  ntp4vc-swipe-left-def $a |- ( ( NTP4VCSwipeLeft A B C D E ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x < E )
      ->
      (
        ( B ` ( NTP4VCShift C ( 1 + x ) ) )
        =
        ( A ` ( NTP4VCShift C x ) )
      )
    )
  ) $.

  ntp4vc-swipe-right-def $a |- ( ( NTP4VCSwipeRight A B C D E ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x < E )
      ->
      (
        ( B ` ( NTP4VCShift C ( x - 1 ) ) )
        =
        ( A ` ( NTP4VCShift C x ) )
      )
    )
  ) $.

  ntp4vc-found-def $a |- ( ( NTP4VCFound A B C D E ) <->
    E. x e. ZZ
    (
      ( A ` ( NTP4VCShift C x ) ) = B
      /\
      ( E <_ ( 1 + x ) /\ ( 2 + x ) <_ ( D + E ) )
    )
  ) $.

  ntp4vc-no-found-def $a |- ( ( NTP4VCNoFound A B C D E ) <->
    A. x e. ZZ
    (
      E <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( D + E )
        ->
        ( A ` ( NTP4VCShift C x ) ) =/= B
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
  $d A B C D E F G H I J K P Q R S $.
  $d x y A B C D E F G H I J K P Q R S $.

  $( Source parameters:
     A=t_3, B=a_3, C=a_4, D=a_2, E=t_2, F=a, G=a_1,
     H=t, I=t_1, J=region, K=linked predicate, P=i, Q=i_1,
     R=x_2, and S=t_4. $)

  ntp4vc-t3-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a4-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- D e. NTP4VCAddr $.
  ntp4vc-t2-map $e |- E e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- F e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- G e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory $e |- I e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- P e. ZZ $.
  ntp4vc-i1-integer $e |- Q e. ZZ $.
  ntp4vc-index-integer $e |- R e. ZZ $.
  ntp4vc-t4-map $e |- S e. ( NTP4VCAddr ^m NTP4VCAddr ) $.

  ntp4vc-item-not-null $e |- B =/= <. 0 , 0 >. $.
  ntp4vc-index-successor-is-upper $e |- ( 1 + R ) = ( P + Q ) $.
  ntp4vc-i1-positive $e |- 0 < Q $.
  ntp4vc-i-nonnegative $e |- 0 <_ P $.

  ntp4vc-region-a2 $e |- ( J ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( J ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a4 $e |- ( J ` ( NTP4VCBase C ) ) <_ 0 $.

  ntp4vc-i-upper $e |- P <_ ( NTP4VCMaxIndex - 1 ) $.
  ntp4vc-sum-upper $e |- ( P + Q ) <_ NTP4VCMaxIndex $.
  ntp4vc-framed-t3 $e |- ( NTP4VCFramed J A ) $.
  ntp4vc-linked-allocation $e |- H e. K $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 P ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 Q ) $.
  ntp4vc-a2-valid $e |- ( NTP4VCValidRW H D 1 ) $.
  ntp4vc-a3-valid $e |- ( NTP4VCValidRW H B 4 ) $.
  ntp4vc-a2-a3-separated $e |- ( NTP4VCSeparated D 1 B 4 ) $.
  ntp4vc-search-lower-sint32 $e |- ( NTP4VCSint32 ( Q - 1 ) ) $.
  ntp4vc-search-upper-sint32 $e |- (
    NTP4VCSint32 ( ( P + Q ) - 1 )
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW H ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-a2-array-separated $e |- (
    NTP4VCSeparated D 1 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-a3-array-separated $e |- (
    NTP4VCSeparated B 4 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-t3-a2-array-separated $e |- (
    NTP4VCSeparated ( A ` D ) 4 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-active-array-valid $e |- (
    NTP4VCValidRW H ( NTP4VCShift C ( Q - 1 ) ) P
  ) $.
  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN H A ( A ` D ) C ( Q - 1 ) P <. 0 , 0 >.
  ) $.
  ntp4vc-index-result $e |- (
    NTP4VCIndexOfEq
      A B C ( Q - 1 ) ( ( P + Q ) - 1 ) R
  ) $.
  ntp4vc-index-sint32 $e |- ( NTP4VCSint32 R ) $.

  ntp4vc-premap-a2-array-separated $e |- (
    NTP4VCSeparated
      ( ( NTP4VCPreMap A C D E F G P Q ) ` D )
      4
      ( NTP4VCShift C 0 )
      NTP4VCMaxIndex
  ) $.
  ntp4vc-item-structure-equal $e |- (
    (
      NTP4VCLoadS1
        B I
        ( NTP4VCPreMap A C D E F G P Q )
    )
    =
    ( NTP4VCLoadS1 B I A )
  ) $.

  ntp4vc-found-last-link $e |- (
    0 < P
    ->
    (
      ( NTP4VCFound A B C P Q )
      ->
      (
        (
          ( NTP4VCM A C D F G P Q )
          `
          ( NTP4VCShift C ( ( P + Q ) - 2 ) )
        )
        =
        ( A ` ( NTP4VCShift C ( ( P + Q ) - 2 ) ) )
      )
    )
  ) $.

  ntp4vc-not-found-no-target-premap $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
          =/=
          B
        )
      )
    )
  ) $.

  ntp4vc-found-no-target-premap $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 3 + x ) <_ ( P + Q )
        ->
        (
          ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
          =/=
          B
        )
      )
    )
  ) $.

  ntp4vc-found-swipe-left $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    (
      NTP4VCSwipeLeft
        ( NTP4VCPreMap A C D E F G P Q )
        A C
        ( ( P + Q ) - 1 )
        ( ( P + Q ) - 2 )
    )
  ) $.

  ntp4vc-not-found-a2-premap-separated $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            D 1
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-a2-premap-separated $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 3 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            D 1
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-target-premap-separated $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            B 4
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-target-premap-separated $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 3 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            B 4
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-premap-array-separated $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
        )
      )
    )
  ) $.

  ntp4vc-found-premap-array-separated $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 3 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCSeparated
            ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
            4 ( NTP4VCShift C 0 ) NTP4VCMaxIndex
        )
      )
    )
  ) $.

  ntp4vc-not-found-linked-premap $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    (
      NTP4VCLinkedN
        H
        ( NTP4VCPreMap A C D E F G P Q )
        ( ( NTP4VCPreMap A C D E F G P Q ) ` D )
        C ( Q - 1 ) P <. 0 , 0 >.
    )
  ) $.

  ntp4vc-found-linked-premap $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    (
      NTP4VCLinkedN
        H
        ( NTP4VCPreMap A C D E F G P Q )
        ( ( NTP4VCPreMap A C D E F G P Q ) ` D )
        C ( Q - 1 ) ( P - 1 ) <. 0 , 0 >.
    )
  ) $.

  ntp4vc-not-found-premap-distinct $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          Q <_ ( 1 + y )
          ->
          (
            ( 2 + x ) <_ ( P + Q )
            ->
            (
              ( 2 + y ) <_ ( P + Q )
              ->
              (
                ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C y ) )
                =/=
                ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-premap-distinct $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          Q <_ ( 1 + y )
          ->
          (
            ( 3 + x ) <_ ( P + Q )
            ->
            (
              ( 3 + y ) <_ ( P + Q )
              ->
              (
                ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C y ) )
                =/=
                ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-unchanged $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    (
      NTP4VCUnchanged
        H
        ( NTP4VCPreMap A C D E F G P Q )
        I A C
        ( Q - 1 )
        ( ( P + Q ) - 2 )
    )
  ) $.

  ntp4vc-not-found-unchanged $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    (
      NTP4VCUnchanged
        H
        ( NTP4VCPreMap A C D E F G P Q )
        I A C
        ( Q - 1 )
        ( ( P + Q ) - 1 )
    )
  ) $.

  ntp4vc-found-structure-shift $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. x e. ZZ
    (
      ( P + Q ) <_ ( 1 + x )
      ->
      (
        ( 3 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCLoadS1
            ( ( NTP4VCM A C D F G P Q ) ` ( NTP4VCShift C x ) )
            I
            ( NTP4VCPreMap A C D E F G P Q )
        )
        =
        (
          NTP4VCLoadS1
            ( A ` ( NTP4VCShift C ( 1 + x ) ) )
            I A
        )
      )
    )
  ) $.

  ntp4vc-not-found-premap-separated $e |- (
    ( NTP4VCNoFound A B C P Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          Q <_ ( 1 + y )
          ->
          (
            ( 2 + x ) <_ ( P + Q )
            ->
            (
              ( 2 + y ) <_ ( P + Q )
              ->
              (
                NTP4VCSeparated
                  ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C y ) )
                  4
                  ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
                  4
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-premap-separated $e |- (
    ( NTP4VCFound A B C P Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          Q <_ ( 1 + y )
          ->
          (
            ( 3 + x ) <_ ( P + Q )
            ->
            (
              ( 3 + y ) <_ ( P + Q )
              ->
              (
                NTP4VCSeparated
                  ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C y ) )
                  4
                  ( ( NTP4VCPreMap A C D E F G P Q ) ` ( NTP4VCShift C x ) )
                  4
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-original-sint-items-not-target $e |- A. x e. ZZ
  (
    Q <_ ( 1 + x )
    ->
    (
      ( 2 + x ) <_ ( P + Q )
      ->
      (
        ( NTP4VCSint32 x )
        ->
        ( A ` ( NTP4VCShift C x ) ) =/= B
      )
    )
  ) $.

  ntp4vc-a2-original-items-separated $e |- A. x e. ZZ
  (
    Q <_ ( 1 + x )
    ->
    (
      ( 2 + x ) <_ ( P + Q )
      ->
      ( NTP4VCSeparated D 1 ( A ` ( NTP4VCShift C x ) ) 4 )
    )
  ) $.

  ntp4vc-original-items-array-separated $e |- A. x e. ZZ
  (
    Q <_ ( 1 + x )
    ->
    (
      ( 2 + x ) <_ ( P + Q )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C x ) ) 4
          ( NTP4VCShift C 0 ) NTP4VCMaxIndex
      )
    )
  ) $.

  ntp4vc-target-original-item-separated $e |- A. x e. ZZ
  (
    ( A ` ( NTP4VCShift C x ) ) =/= B
    ->
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        ( NTP4VCSeparated B 4 ( A ` ( NTP4VCShift C x ) ) 4 )
      )
    )
  ) $.

  ntp4vc-original-items-distinct $e |- A. y e. ZZ A. x e. ZZ
  (
    y =/= x
    ->
    (
      Q <_ ( 1 + x )
      ->
      (
        Q <_ ( 1 + y )
        ->
        (
          ( 2 + x ) <_ ( P + Q )
          ->
          (
            ( 2 + y ) <_ ( P + Q )
            ->
            ( A ` ( NTP4VCShift C y ) ) =/= ( A ` ( NTP4VCShift C x ) )
          )
        )
      )
    )
  ) $.

  ntp4vc-original-items-separated $e |- A. y e. ZZ A. x e. ZZ
  (
    y =/= x
    ->
    (
      Q <_ ( 1 + x )
      ->
      (
        Q <_ ( 1 + y )
        ->
        (
          ( 2 + x ) <_ ( P + Q )
          ->
          (
            ( 2 + y ) <_ ( P + Q )
            ->
            (
              NTP4VCSeparated
                ( A ` ( NTP4VCShift C y ) ) 4
                ( A ` ( NTP4VCShift C x ) ) 4
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a14-a2-eq-a10 $e |- (
    (
      ( NTP4VCA14 A B C D E F G P Q S )
      `
      D
    )
    =
    (
      ( NTP4VCPreMap A C D E F G P Q )
      `
      D
    )
  ) $.

  ntp4vc-a14-a2-array-separated $e |- (
    NTP4VCSeparated
      (
        ( NTP4VCA14 A B C D E F G P Q S )
        `
        D
      )
      4
      ( NTP4VCShift C 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a2-a14-nodes-separated $e |- A. x e. ZZ
  (
    Q <_ x
    ->
    (
      x < ( P + Q )
      ->
      (
        NTP4VCSeparated
          D 1
          (
            ( NTP4VCA14 A B C D E F G P Q S )
            `
            ( NTP4VCShift C x )
          )
          4
      )
    )
  ) $.

  ntp4vc-a14-nodes-array-separated $e |- A. x e. ZZ
  (
    Q <_ x
    ->
    (
      x < ( P + Q )
      ->
      (
        NTP4VCSeparated
          (
            ( NTP4VCA14 A B C D E F G P Q S )
            `
            ( NTP4VCShift C x )
          )
          4
          ( NTP4VCShift C 0 )
          NTP4VCMaxIndex
      )
    )
  ) $.

  ntp4vc-a14-nodes-separated $e |- A. y e. ZZ A. x e. ZZ
  (
    y =/= x
    ->
    (
      Q <_ x
      ->
      (
        Q <_ y
        ->
        (
          x < ( P + Q )
          ->
          (
            y < ( P + Q )
            ->
            (
              NTP4VCSeparated
                (
                  ( NTP4VCA14 A B C D E F G P Q S )
                  `
                  ( NTP4VCShift C y )
                )
                4
                (
                  ( NTP4VCA14 A B C D E F G P Q S )
                  `
                  ( NTP4VCShift C x )
                )
                4
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a14-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
  (
    y =/= x
    ->
    (
      ( Q - 1 ) <_ x
      ->
      (
        ( Q - 1 ) <_ y
        ->
        (
          x < ( P + Q )
          ->
          (
            y < ( P + Q )
            ->
            (
              (
                ( NTP4VCA14 A B C D E F G P Q S )
                `
                ( NTP4VCShift C y )
              )
              =/=
              (
                ( NTP4VCA14 A B C D E F G P Q S )
                `
                ( NTP4VCShift C x )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a14-swipe-right $e |- (
    NTP4VCSwipeRight
      ( NTP4VCA14 A B C D E F G P Q S )
      ( NTP4VCPreMap A C D E F G P Q )
      C Q ( P + Q )
  ) $.

  ntp4vc-a14-linked $e |- (
    NTP4VCLinkedN
      H
      ( NTP4VCA14 A B C D E F G P Q S )
      (
        ( NTP4VCPreMap A C D E F G P Q )
        `
        D
      )
      C Q P <. 0 , 0 >.
  ) $.

  ntp4vc__metamath__frama_c_contiki_list_list_push_Why3_ide_VClist_push_stmt_post_part1_goal44
    $a |- (
      NTP4VCUnchanged
        H
        ( NTP4VCFinalMap A B C D E F G P Q S )
        I
        ( NTP4VCStageMap A B C D E F G P Q S )
        C
        ( Q - 1 )
        ( P + Q )
    ) $.
$}
