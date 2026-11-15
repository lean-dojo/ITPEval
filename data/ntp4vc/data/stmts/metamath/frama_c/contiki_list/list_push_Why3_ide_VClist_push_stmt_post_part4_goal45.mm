$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_push_Why3_ide_VClist_push_stmt_post_part4_goal45:
  the list-push verification condition preserves the unchanged array-backed
  linked-list region after index search, pointer-map havoc, and functional
  updates, under the generated integer bounds, validity, linkage, structure,
  separation, distinctness, swipe, and branch assumptions. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ. The definitions below
  expand shift, separation, writable validity, signed-32-bit range, framing,
  functional update, havoc, structure loading, left swipe, and unchangedness.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate,
  using an integer-indexed finite chain. NTP4VCIndexOfEq is the graph of the
  source first-match l_index_of operation on its full integer interval.
  NTP4VCFound and NTP4VCNoFound retain the source existential and universal
  branch conditions over all integers. NTP4VCTarget, NTP4VCA10, NTP4VCA14,
  NTP4VCA12, and NTP4VCFinalMap name only deterministic source let-bound terms.
  NTP4VCLoadS1 retains the pointer field and all three real fields.

  The arbitrary source region function and linked predicate are retained as
  an integer map and a subset of integer maps. The final declaration is
  Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCUpdate NTP4VCTarget NTP4VCA10 NTP4VCA14 NTP4VCA12
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
ntp4vc-target-class $a class ( NTP4VCTarget A B C ) $.
ntp4vc-a10-class
  $a class ( NTP4VCA10 A B C D E F G H I ) $.
ntp4vc-a14-class
  $a class ( NTP4VCA14 A B C D E F G H I J ) $.
ntp4vc-a12-class
  $a class ( NTP4VCA12 A B C D E F G H I J K ) $.
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

ntp4vc-target-def $a |- (
  NTP4VCTarget A B C
) =
  ( A ` ( NTP4VCShift B C ) ) $.

ntp4vc-a10-def $a |- (
  NTP4VCA10 A B C D E F G H I
) =
  (
    NTP4VCHavoc
      D
      (
        NTP4VCUpdate
          ( NTP4VCUpdate A C E )
          (
            NTP4VCShift
              ( A ` ( NTP4VCShift B ( I - 1 ) ) )
              0
          )
          F
      )
      ( NTP4VCShift B I )
      ( ( G + H ) - I )
  ) $.

ntp4vc-a14-def $a |- (
  NTP4VCA14 A B C D E F G H I J
) =
  (
    NTP4VCHavoc
      J
      ( NTP4VCA10 A B C D E F G H I )
      ( NTP4VCShift B ( H - 1 ) )
      ( 1 + G )
  ) $.

ntp4vc-a12-def $a |- (
  NTP4VCA12 A B C D E F G H I J K
) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          ( NTP4VCA14 A B D E F G H I J K )
          ( NTP4VCShift ( NTP4VCTarget A B C ) 0 )
          ( ( NTP4VCA10 A B D E F G H I J ) ` D )
      )
      ( NTP4VCShift B ( I - 1 ) )
      ( NTP4VCTarget A B C )
  ) $.

ntp4vc-final-map-def $a |- (
  NTP4VCFinalMap A B C D E F G H I J K
) =
  (
    NTP4VCUpdate
      ( NTP4VCA12 A B C D E F G H I J K )
      D
      ( NTP4VCTarget A B C )
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
      ( x < D /\ E <_ ( 1 + x ) )
    )
  ) $.

  ntp4vc-no-found-def $a |- ( ( NTP4VCNoFound A B C D E ) <->
    A. x e. ZZ
    (
      x < D
      ->
      (
        E <_ ( 1 + x )
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
  $d f x y A B C D E F G H I J K P Q R S $.

  $( Source parameters:
     A=t_3, B=a_3, C=i_2, D=a_2, E=t_2, F=a, G=a_1,
     H=t, I=t_1, J=region, K=linked predicate, P=i, Q=i_1,
     R=x_2, and S=t_4. The let-bound a_4 is NTP4VCTarget A B C. $)

  ntp4vc-t3-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- C e. ZZ $.
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

  ntp4vc-item-not-null $e |- (
    ( NTP4VCTarget A B C ) =/= <. 0 , 0 >.
  ) $.
  ntp4vc-index-not-upper $e |- ( ( P + Q ) =/= R ) $.
  ntp4vc-i1-positive $e |- 0 < Q $.
  ntp4vc-i2-below-upper $e |- C < ( P + Q ) $.

  ntp4vc-region-a2 $e |- ( J ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( J ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-item $e |- (
    ( J ` ( NTP4VCBase ( NTP4VCTarget A B C ) ) ) <_ 0
  ) $.

  ntp4vc-index-strict-upper $e |- R < ( P + Q ) $.
  ntp4vc-index-upper $e |- R <_ ( P + Q ) $.
  ntp4vc-i-lower $e |- -u 1 <_ P $.
  ntp4vc-i-upper $e |- P <_ ( NTP4VCMaxIndex - 2 ) $.
  ntp4vc-sum-upper $e |- ( P + Q ) <_ ( NTP4VCMaxIndex - 1 ) $.
  ntp4vc-i1-i2-bound $e |- Q <_ ( 1 + C ) $.
  ntp4vc-i1-index-bound $e |- Q <_ ( 1 + R ) $.

  ntp4vc-framed-t3 $e |- ( NTP4VCFramed J A ) $.
  ntp4vc-linked-allocation $e |- H e. K $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 P ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 Q ) $.
  ntp4vc-a2-valid $e |- ( NTP4VCValidRW H D 1 ) $.
  ntp4vc-search-lower-sint32 $e |- ( NTP4VCSint32 ( Q - 1 ) ) $.
  ntp4vc-length-sint32 $e |- ( NTP4VCSint32 ( 1 + P ) ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      H
      ( NTP4VCShift B 0 )
      NTP4VCMaxIndex
  ) $.
  ntp4vc-item-valid $e |- (
    NTP4VCValidRW H ( NTP4VCTarget A B C ) 4
  ) $.
  ntp4vc-a2-array-separated $e |- (
    NTP4VCSeparated D 1 ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-root-array-separated $e |- (
    NTP4VCSeparated
      ( A ` D ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-a2-item-separated $e |- (
    NTP4VCSeparated D 1 ( NTP4VCTarget A B C ) 4
  ) $.
  ntp4vc-item-array-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCTarget A B C ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-active-array-valid $e |- (
    NTP4VCValidRW H ( NTP4VCShift B ( Q - 1 ) ) ( 1 + P )
  ) $.
  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN
      H A ( A ` D ) B ( Q - 1 ) ( 1 + P ) <. 0 , 0 >.
  ) $.
  ntp4vc-index-result $e |- (
    NTP4VCIndexOfEq
      A ( NTP4VCTarget A B C ) B
      ( Q - 1 ) ( P + Q ) R
  ) $.
  ntp4vc-index-sint32 $e |- ( NTP4VCSint32 R ) $.

  ntp4vc-a11-array-separated $e |- (
    NTP4VCSeparated
      ( ( NTP4VCA10 A B D E F G P Q R ) ` D )
      4
      ( NTP4VCShift B 0 )
      NTP4VCMaxIndex
  ) $.
  ntp4vc-item-structure-equal $e |- (
    (
      NTP4VCLoadS1
        ( NTP4VCTarget A B C )
        I
        ( NTP4VCA10 A B D E F G P Q R )
    )
    =
    ( NTP4VCLoadS1 ( NTP4VCTarget A B C ) I A )
  ) $.

  ntp4vc-found-last-link $e |- (
    Q <_ R
    ->
    (
      ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
      ->
      (
        (
          NTP4VCA10 A B D E F G P Q R
          `
          ( NTP4VCShift B ( R - 1 ) )
        )
        =
        ( A ` ( NTP4VCShift B ( R - 1 ) ) )
      )
    )
  ) $.

  ntp4vc-found-swipe-left $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    (
      NTP4VCSwipeLeft
        ( NTP4VCA10 A B D E F G P Q R )
        A B R ( ( P + Q ) - 1 )
    )
  ) $.

  ntp4vc-not-found-no-target-a10 $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      x < ( P + Q )
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          (
            NTP4VCA10 A B D E F G P Q R
            `
            ( NTP4VCShift B x )
          )
          =/=
          ( NTP4VCTarget A B C )
        )
      )
    )
  ) $.

  ntp4vc-found-no-target-a10 $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      Q <_ ( 1 + x )
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          (
            NTP4VCA10 A B D E F G P Q R
            `
            ( NTP4VCShift B x )
          )
          =/=
          ( NTP4VCTarget A B C )
        )
      )
    )
  ) $.

  ntp4vc-found-linked-a10 $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    (
      NTP4VCLinkedN
        H
        ( NTP4VCA10 A B D E F G P Q R )
        ( ( NTP4VCA10 A B D E F G P Q R ) ` D )
        B ( Q - 1 ) P <. 0 , 0 >.
    )
  ) $.

  ntp4vc-not-found-linked-a10 $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    (
      NTP4VCLinkedN
        H
        ( NTP4VCA10 A B D E F G P Q R )
        ( ( NTP4VCA10 A B D E F G P Q R ) ` D )
        B ( Q - 1 ) ( 1 + P ) <. 0 , 0 >.
    )
  ) $.

  ntp4vc-not-found-unchanged $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    (
      NTP4VCUnchanged
        H
        ( NTP4VCA10 A B D E F G P Q R )
        I A B ( Q - 1 ) ( P + Q )
    )
  ) $.

  ntp4vc-found-unchanged $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    (
      NTP4VCUnchanged
        H
        ( NTP4VCA10 A B D E F G P Q R )
        I A B ( Q - 1 ) ( R - 1 )
    )
  ) $.

  ntp4vc-not-found-a2-a10-separated $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      x < ( P + Q )
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            D 1
            (
              NTP4VCA10 A B D E F G P Q R
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-a2-a10-separated $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
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
            (
              NTP4VCA10 A B D E F G P Q R
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-item-a10-separated $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      x < ( P + Q )
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            ( NTP4VCTarget A B C ) 4
            (
              NTP4VCA10 A B D E F G P Q R
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-found-item-a10-separated $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
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
            ( NTP4VCTarget A B C ) 4
            (
              NTP4VCA10 A B D E F G P Q R
              `
              ( NTP4VCShift B x )
            )
            4
        )
      )
    )
  ) $.

  ntp4vc-not-found-a10-array-separated $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      x < ( P + Q )
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            (
              NTP4VCA10 A B D E F G P Q R
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

  ntp4vc-found-a10-array-separated $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
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
            (
              NTP4VCA10 A B D E F G P Q R
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

  ntp4vc-found-successor-loads $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. x e. ZZ
    (
      R <_ x
      ->
      (
        ( 2 + x ) <_ ( P + Q )
        ->
        (
          NTP4VCLoadS1
            (
              NTP4VCA10 A B D E F G P Q R
              `
              ( NTP4VCShift B x )
            )
            I
            ( NTP4VCA10 A B D E F G P Q R )
          =
          NTP4VCLoadS1
            ( A ` ( NTP4VCShift B ( 1 + x ) ) )
            I A
        )
      )
    )
  ) $.

  ntp4vc-not-found-a10-distinct $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( P + Q )
        ->
        (
          y < ( P + Q )
          ->
          (
            Q <_ ( 1 + x )
            ->
            (
              Q <_ ( 1 + y )
              ->
              (
                (
                  NTP4VCA10 A B D E F G P Q R
                  `
                  ( NTP4VCShift B y )
                )
                =/=
                (
                  NTP4VCA10 A B D E F G P Q R
                  `
                  ( NTP4VCShift B x )
                )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-found-a10-distinct $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
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
                (
                  NTP4VCA10 A B D E F G P Q R
                  `
                  ( NTP4VCShift B y )
                )
                =/=
                (
                  NTP4VCA10 A B D E F G P Q R
                  `
                  ( NTP4VCShift B x )
                )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-not-found-a10-separated $e |- (
    ( NTP4VCNoFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      y =/= x
      ->
      (
        x < ( P + Q )
        ->
        (
          y < ( P + Q )
          ->
          (
            Q <_ ( 1 + x )
            ->
            (
              Q <_ ( 1 + y )
              ->
              (
                NTP4VCSeparated
                  (
                    NTP4VCA10 A B D E F G P Q R
                    `
                    ( NTP4VCShift B y )
                  )
                  4
                  (
                    NTP4VCA10 A B D E F G P Q R
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

  ntp4vc-found-a10-separated $e |- (
    ( NTP4VCFound A ( NTP4VCTarget A B C ) B ( P + Q ) Q )
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
                  (
                    NTP4VCA10 A B D E F G P Q R
                    `
                    ( NTP4VCShift B y )
                  )
                  4
                  (
                    NTP4VCA10 A B D E F G P Q R
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

  ntp4vc-a2-original-items-separated $e |- A. x e. ZZ
  (
    x < ( P + Q )
    ->
    (
      Q <_ ( 1 + x )
      ->
      (
        NTP4VCSeparated
          D 1
          ( A ` ( NTP4VCShift B x ) )
          4
      )
    )
  ) $.

  ntp4vc-original-items-array-separated $e |- A. x e. ZZ
  (
    x < ( P + Q )
    ->
    (
      Q <_ ( 1 + x )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift B x ) )
          4
          ( NTP4VCShift B 0 )
          NTP4VCMaxIndex
      )
    )
  ) $.

  ntp4vc-item-original-item-separated $e |- A. x e. ZZ
  (
    ( NTP4VCTarget A B C ) =/= ( A ` ( NTP4VCShift B x ) )
    ->
    (
      x < ( P + Q )
      ->
      (
        Q <_ ( 1 + x )
        ->
        (
          NTP4VCSeparated
            ( NTP4VCTarget A B C )
            4
            ( A ` ( NTP4VCShift B x ) )
            4
        )
      )
    )
  ) $.

  ntp4vc-original-items-distinct $e |- A. y e. ZZ A. x e. ZZ
  (
    y =/= x
    ->
    (
      x < ( P + Q )
      ->
      (
        y < ( P + Q )
        ->
        (
          Q <_ ( 1 + x )
          ->
          (
            Q <_ ( 1 + y )
            ->
            ( A ` ( NTP4VCShift B y ) ) =/= ( A ` ( NTP4VCShift B x ) )
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
      x < ( P + Q )
      ->
      (
        y < ( P + Q )
        ->
        (
          Q <_ ( 1 + x )
          ->
          (
            Q <_ ( 1 + y )
            ->
            (
              NTP4VCSeparated
                ( A ` ( NTP4VCShift B y ) )
                4
                ( A ` ( NTP4VCShift B x ) )
                4
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a14-a2-eq-a11 $e |- (
    (
      ( NTP4VCA14 A B D E F G P Q R S )
      `
      D
    )
    =
    (
      ( NTP4VCA10 A B D E F G P Q R )
      `
      D
    )
  ) $.

  ntp4vc-a14-a2-array-separated $e |- (
    NTP4VCSeparated
      (
        ( NTP4VCA14 A B D E F G P Q R S )
        `
        D
      )
      4
      ( NTP4VCShift B 0 )
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
            ( NTP4VCA14 A B D E F G P Q R S )
            `
            ( NTP4VCShift B x )
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
            ( NTP4VCA14 A B D E F G P Q R S )
            `
            ( NTP4VCShift B x )
          )
          4
          ( NTP4VCShift B 0 )
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
                  ( NTP4VCA14 A B D E F G P Q R S )
                  `
                  ( NTP4VCShift B y )
                )
                4
                (
                  ( NTP4VCA14 A B D E F G P Q R S )
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
                ( NTP4VCA14 A B D E F G P Q R S )
                `
                ( NTP4VCShift B y )
              )
              =/=
              (
                ( NTP4VCA14 A B D E F G P Q R S )
                `
                ( NTP4VCShift B x )
              )
            )
          )
        )
      )
    )
  ) $.

  ntp4vc-a14-swipe-right $e |- (
    NTP4VCSwipeRight
      ( NTP4VCA14 A B D E F G P Q R S )
      ( NTP4VCA10 A B D E F G P Q R )
      B Q ( P + Q )
  ) $.

  ntp4vc-a14-linked $e |- (
    NTP4VCLinkedN
      H
      ( NTP4VCA14 A B D E F G P Q R S )
      (
        ( NTP4VCA10 A B D E F G P Q R )
        `
        D
      )
      B Q P <. 0 , 0 >.
  ) $.

  ntp4vc__metamath__frama_c_contiki_list_list_push_Why3_ide_VClist_push_stmt_post_part4_goal45
    $a |- (
      NTP4VCUnchanged
        H
        ( NTP4VCFinalMap A B C D E F G P Q R S )
        I
        ( NTP4VCA12 A B C D E F G P Q R S )
        B
        ( Q - 1 )
        ( P + Q )
    ) $.
$}
