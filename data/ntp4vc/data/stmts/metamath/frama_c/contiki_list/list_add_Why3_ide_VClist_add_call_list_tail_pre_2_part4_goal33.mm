$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_tail_pre_2_part4_goal33:
  the list-add tail-call verification condition preserves a linked segment
  after a bounded index search, havoc, and null-pointer update, under the
  generated integer, memory-validity, framing, structure, distinctness, and
  separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented by ZZ X. ZZ. The definitions below expand the
  source shift, separation, writable-validity, signed-32-bit, framing,
  functional-update, havoc, structure-load, swipe, and unchanged operations.
  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate,
  using an integer-indexed finite pointer chain.

  NTP4VCIndexOfEq is the exact functional graph of l_index_of: it selects the
  first matching position in the half-open interval or its upper endpoint.
  Thus the source let-bound x_1 is represented by an integer variable with
  its exact graph equation, without changing its quantifier scope.

  NTP4VCPreMap and NTP4VCFinalMap name the source let-bound maps a_7 and a_8.
  NTP4VCLoadS1 retains all four fields of load_s1_list. The arbitrary source
  region function and linked predicate remain an integer map and a subset of
  integer maps. All integer quantifiers range over ZZ. The final declaration
  is Metamath's native unproved $a statement encoding; there is no $p proof.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCHavoc NTP4VCUpdate NTP4VCMid
  NTP4VCA4 NTP4VCX NTP4VCX3 NTP4VCX4
  NTP4VCPreMap NTP4VCFinalMap NTP4VCLoadS1
  NTP4VCLinkedN NTP4VCIndexOfEq NTP4VCSwipeLeft NTP4VCUnchanged
  NTP4VCInRange NTP4VCNoRange
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-mid-class $a class ( NTP4VCMid A B C D E ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-x4-class $a class ( NTP4VCX4 A ) $.
ntp4vc-pre-map-class
  $a class ( NTP4VCPreMap A B C D E F G H I ) $.
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
  $a wff ( NTP4VCSwipeLeft A B C D P ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D P ) $.
ntp4vc-in-range-syntax
  $a wff ( NTP4VCInRange A B C D E ) $.
ntp4vc-no-range-syntax
  $a wff ( NTP4VCNoRange A B C D E ) $.

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

ntp4vc-mid-def $a |- ( NTP4VCMid A B C D E ) =
  (
    NTP4VCUpdate
      ( NTP4VCUpdate A B C )
      ( NTP4VCShift ( A ` D ) 0 )
      E
  ) $.

ntp4vc-a4-def $a |- ( NTP4VCA4 A B C ) =
  ( A ` ( NTP4VCShift B C ) ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( ( 1 + A ) + B ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) = ( A + B ) $.
ntp4vc-x4-def $a |- ( NTP4VCX4 A ) = ( 1 + A ) $.

ntp4vc-pre-map-def $a |- (
  NTP4VCPreMap A B C D E F G H I
) =
  (
    NTP4VCHavoc
      D
      ( NTP4VCMid A E F ( NTP4VCShift B ( C - 1 ) ) G )
      ( NTP4VCShift B C )
      ( ( ( 1 + H ) + I ) - C )
  ) $.

ntp4vc-final-map-def $a |- (
  NTP4VCFinalMap A B C D E F G H I J
) =
  (
    NTP4VCUpdate
      ( NTP4VCPreMap A B D E F G H I J )
      ( NTP4VCShift ( NTP4VCA4 A B C ) 0 )
      <. 0 , 0 >.
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
          A ` ( NTP4VCShift ( A ` ( NTP4VCShift C x ) ) 0 )
        )
        =
        (
          B ` ( NTP4VCShift ( B ` ( NTP4VCShift C x ) ) 0 )
        )
      )
    )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-in-range-def $a |- ( ( NTP4VCInRange A B C D E ) <->
    E. x e. ZZ
    (
      B = ( A ` ( NTP4VCShift C x ) )
      /\
      ( D <_ x /\ x <_ E )
    )
  ) $.

  ntp4vc-no-range-def $a |- ( ( NTP4VCNoRange A B C D E ) <->
    A. x e. ZZ
    (
      ( D <_ x /\ x <_ E )
      ->
      B =/= ( A ` ( NTP4VCShift C x ) )
    )
  ) $.
$}

${
  $d A B C D E F G H I J K L M N $.
  $d x y A B C D E F G H I J K L M N $.

  $( Source parameters:
     A=t_3, B=a_3, C=i_2, D=i, E=i_1, F=t_2, G=a_2,
     H=a, I=a_1, J=t, K=t_1, L=region, M=linked extension,
     N=x_1, constrained by the exact l_index_of graph below. $)

  ntp4vc-t3-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a3-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- C e. ZZ $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-t2-map $e |- F e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a2-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a-address $e |- H e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- I e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory $e |- K e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- M C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-integer $e |- N e. ZZ $.

  ntp4vc-a4-not-null $e |- ( NTP4VCA4 A B C ) =/= <. 0 , 0 >. $.
  ntp4vc-index-result $e |- (
    NTP4VCIndexOfEq A ( NTP4VCA4 A B C ) B E
      ( NTP4VCX D E ) N
  ) $.
  ntp4vc-index-before-upper $e |- ( NTP4VCX D E ) =/= N $.
  ntp4vc-a9-not-null $e |- (
    ( ( NTP4VCFinalMap A B C N F G H I D E ) ` G )
    =/= <. 0 , 0 >.
  ) $.

  ntp4vc-i1-nonnegative $e |- 0 <_ E $.
  ntp4vc-i1-le-i2 $e |- E <_ C $.
  ntp4vc-i2-le-x3 $e |- C <_ ( NTP4VCX3 D E ) $.
  ntp4vc-region-a2 $e |- ( L ` ( NTP4VCBase G ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( L ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a4 $e |- (
    ( L ` ( NTP4VCBase ( NTP4VCA4 A B C ) ) ) <_ 0
  ) $.
  ntp4vc-i1-le-index $e |- E <_ N $.
  ntp4vc-index-le-x3 $e |- N <_ ( NTP4VCX3 D E ) $.
  ntp4vc-i-lower-bound $e |- -u 1 <_ D $.
  ntp4vc-i-upper-bound $e |- D <_ ( NTP4VCMaxIndex - 2 ) $.
  ntp4vc-i1-upper-bound $e |- E <_ ( NTP4VCMaxIndex - 1 ) $.
  ntp4vc-x3-upper-bound $e |- (
    ( NTP4VCX3 D E ) <_ ( NTP4VCMaxIndex - 2 )
  ) $.
  ntp4vc-index-le-x $e |- N <_ ( NTP4VCX D E ) $.

  ntp4vc-framed-t3 $e |- ( NTP4VCFramed L A ) $.
  ntp4vc-linked-allocation $e |- J e. M $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-a2-valid $e |- ( NTP4VCValidRW J G 1 ) $.
  ntp4vc-x4-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX4 D ) ) $.
  ntp4vc-array-valid $e |- (
    NTP4VCValidRW J ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-array-suffix-valid $e |- (
    NTP4VCValidRW J ( NTP4VCShift B E ) ( NTP4VCX4 D )
  ) $.
  ntp4vc-a4-valid $e |- (
    NTP4VCValidRW J ( NTP4VCA4 A B C ) 4
  ) $.
  ntp4vc-a2-array-separated $e |- (
    NTP4VCSeparated G 1 ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-t3-a2-array-separated $e |- (
    NTP4VCSeparated ( A ` G ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-a2-a4-separated $e |- (
    NTP4VCSeparated G 1 ( NTP4VCA4 A B C ) 4
  ) $.
  ntp4vc-a4-array-separated $e |- (
    NTP4VCSeparated ( NTP4VCA4 A B C ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN J A ( A ` G ) B E
      ( NTP4VCX4 D ) <. 0 , 0 >.
  ) $.
  ntp4vc-index-sint32 $e |- ( NTP4VCSint32 N ) $.
  ntp4vc-premap-a2-array-separated $e |- (
    NTP4VCSeparated
      ( ( NTP4VCPreMap A B N F G H I D E ) ` G ) 4
      ( NTP4VCShift B 0 ) NTP4VCMaxIndex
  ) $.
  ntp4vc-a4-structure-equal $e |- (
    NTP4VCLoadS1 ( NTP4VCA4 A B C ) K
      ( NTP4VCPreMap A B N F G H I D E )
    =
    NTP4VCLoadS1 ( NTP4VCA4 A B C ) K A
  ) $.

  ntp4vc-found-link $e |- (
    E < N
    ->
    (
      ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
          ( NTP4VCX3 D E ) )
      ->
      (
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B ( N - 1 ) ) )
        =
        ( A ` ( NTP4VCShift B ( N - 1 ) ) )
      )
    )
  ) $.
  ntp4vc-found-swipe-left $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    ( NTP4VCSwipeLeft
        ( NTP4VCPreMap A B N F G H I D E )
        A B N ( NTP4VCX3 D E ) )
  ) $.
  ntp4vc-found-no-a4-premap $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x < ( NTP4VCX3 D E ) )
      ->
      (
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B x ) )
        =/= ( NTP4VCA4 A B C )
      )
    )
  ) $.
  ntp4vc-not-found-no-a4-premap $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      (
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B x ) )
        =/= ( NTP4VCA4 A B C )
      )
    )
  ) $.
  ntp4vc-found-linked-premap $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    ( NTP4VCLinkedN J
        ( NTP4VCPreMap A B N F G H I D E )
        ( ( NTP4VCPreMap A B N F G H I D E ) ` G )
        B E D <. 0 , 0 >. )
  ) $.
  ntp4vc-not-found-linked-premap $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    ( NTP4VCLinkedN J
        ( NTP4VCPreMap A B N F G H I D E )
        ( ( NTP4VCPreMap A B N F G H I D E ) ` G )
        B E ( NTP4VCX4 D ) <. 0 , 0 >. )
  ) $.
  ntp4vc-not-found-unchanged $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    ( NTP4VCUnchanged
        ( NTP4VCPreMap A B N F G H I D E )
        A B E ( NTP4VCX D E ) )
  ) $.
  ntp4vc-found-unchanged $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    ( NTP4VCUnchanged
        ( NTP4VCPreMap A B N F G H I D E )
        A B E ( N - 1 ) )
  ) $.

  ntp4vc-found-a2-premap-separated $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x < ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated G 1
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.
  ntp4vc-not-found-a2-premap-separated $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated G 1
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.
  ntp4vc-found-a4-premap-separated $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x < ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated ( NTP4VCA4 A B C ) 4
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.
  ntp4vc-not-found-a4-premap-separated $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated ( NTP4VCA4 A B C ) 4
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.
  ntp4vc-found-premap-array-separated $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x < ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4
          ( NTP4VCShift B 0 ) NTP4VCMaxIndex )
    )
  ) $.
  ntp4vc-not-found-premap-array-separated $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4
          ( NTP4VCShift B 0 ) NTP4VCMaxIndex )
    )
  ) $.

  ntp4vc-found-structure-swipe $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. x e. ZZ
    (
      ( N <_ x /\ x < ( NTP4VCX3 D E ) )
      ->
      (
        NTP4VCLoadS1
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) )
          K ( NTP4VCPreMap A B N F G H I D E )
        =
        NTP4VCLoadS1
          ( A ` ( NTP4VCShift B ( 1 + x ) ) ) K A
      )
    )
  ) $.

  ntp4vc-found-premap-distinct $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        ( E <_ x /\ ( E <_ y /\
          ( x < ( NTP4VCX3 D E ) /\ y < ( NTP4VCX3 D E ) ) ) )
      )
      ->
      (
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B y ) )
        =/=
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B x ) )
      )
    )
  ) $.
  ntp4vc-not-found-premap-distinct $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        ( E <_ x /\ ( E <_ y /\
          ( x <_ ( NTP4VCX3 D E ) /\ y <_ ( NTP4VCX3 D E ) ) ) )
      )
      ->
      (
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B y ) )
        =/=
        ( NTP4VCPreMap A B N F G H I D E
          ` ( NTP4VCShift B x ) )
      )
    )
  ) $.
  ntp4vc-found-premap-pair-separated $e |- (
    ( NTP4VCInRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        ( E <_ x /\ ( E <_ y /\
          ( x < ( NTP4VCX3 D E ) /\ y < ( NTP4VCX3 D E ) ) ) )
      )
      ->
      ( NTP4VCSeparated
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B y ) ) 4
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.
  ntp4vc-not-found-premap-pair-separated $e |- (
    ( NTP4VCNoRange A ( NTP4VCA4 A B C ) B E
        ( NTP4VCX3 D E ) )
    ->
    A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        ( E <_ x /\ ( E <_ y /\
          ( x <_ ( NTP4VCX3 D E ) /\ y <_ ( NTP4VCX3 D E ) ) ) )
      )
      ->
      ( NTP4VCSeparated
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B y ) ) 4
          ( NTP4VCPreMap A B N F G H I D E
            ` ( NTP4VCShift B x ) ) 4 )
    )
  ) $.

  ntp4vc-a2-t3-node-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated G 1 ( A ` ( NTP4VCShift B x ) ) 4 )
    ) $.
  ntp4vc-t3-node-array-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x <_ ( NTP4VCX3 D E ) )
      ->
      ( NTP4VCSeparated ( A ` ( NTP4VCShift B x ) ) 4
          ( NTP4VCShift B 0 ) NTP4VCMaxIndex )
    ) $.
  ntp4vc-a4-t3-node-separated $e |- A. x e. ZZ
    (
      ( NTP4VCA4 A B C ) =/= ( A ` ( NTP4VCShift B x ) )
      ->
      (
        E <_ x
        ->
        (
          x <_ ( NTP4VCX3 D E )
          ->
          ( NTP4VCSeparated ( NTP4VCA4 A B C ) 4
              ( A ` ( NTP4VCShift B x ) ) 4 )
        )
      )
    ) $.
  ntp4vc-t3-node-distinct $e |- A. y e. ZZ A. x e. ZZ
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
            x <_ ( NTP4VCX3 D E )
            ->
            (
              y <_ ( NTP4VCX3 D E )
              ->
              ( A ` ( NTP4VCShift B y ) )
                =/= ( A ` ( NTP4VCShift B x ) )
            )
          )
        )
      )
    ) $.
  ntp4vc-t3-node-pair-separated $e |- A. y e. ZZ A. x e. ZZ
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
            x <_ ( NTP4VCX3 D E )
            ->
            (
              y <_ ( NTP4VCX3 D E )
              ->
              ( NTP4VCSeparated
                  ( A ` ( NTP4VCShift B y ) ) 4
                  ( A ` ( NTP4VCShift B x ) ) 4 )
            )
          )
        )
      )
    ) $.

  ntp4vc-list-add-call-list-tail-pre-2-part4-goal33
    $a |- (
      NTP4VCLinkedN
        J
        ( NTP4VCFinalMap A B C N F G H I D E )
        ( ( NTP4VCFinalMap A B C N F G H I D E ) ` G )
        B E D <. 0 , 0 >.
    ) $.
$}
