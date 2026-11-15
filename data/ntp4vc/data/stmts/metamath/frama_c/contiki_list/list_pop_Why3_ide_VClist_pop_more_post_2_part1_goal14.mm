$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_pop_Why3_ide_VClist_pop_more_post_2_part1_goal14:
  the list-pop verification condition establishes a left-swipe relation after
  updating one pointer-map entry, under the generated integer bounds, memory
  validity, framing, linkage, linked-segment, distinctness, and separation
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCFramed, and NTP4VCUpdate expand the corresponding
  source definitions. The source region function is an arbitrary integer map,
  and the source linked predicate is an arbitrary subset of integer maps.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  existentially quantified integer-indexed address function records the
  finite chain from the root at position zero to the bound at position n. At
  each integer position in the chain it preserves the array lookup,
  writable-node condition, and next-pointer step, together with the source
  index and length bounds.

  NTP4VCSwipeLeft directly expands p_array_swipe_left. The source let-bound
  addresses and integer are expanded at every use, all source integer
  quantifiers range over the full set ZZ, and the pointer update is functional
  update on the full address domain. The final declaration is Metamath's
  native unproved $a statement encoding; this database adds no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCUpdate NTP4VCLinkedN NTP4VCSwipeLeft
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.

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
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
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
  $d A B C D E F G H I $.
  $d x y A B C D E F G H I $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, D=i, E=i_1, F=t,
     G=region, H=linked extension, I=t_2. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-post-pointer-map $e |- I e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.

  ntp4vc-a2-nonnull $e |- ( A ` B ) =/= <. 0 , 0 >. $.

  ntp4vc-i-positive $e |- 0 < D $.
  ntp4vc-i1-nonnegative $e |- 0 <_ E $.

  ntp4vc-region-a $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( G ` ( NTP4VCBase C ) ) <_ 0
  ) $.

  ntp4vc-framed-pointer-map $e |- (
    NTP4VCFramed G A
  ) $.

  ntp4vc-linked-allocation $e |- F e. H $.

  ntp4vc-i-sint32 $e |- (
    NTP4VCSint32 D
  ) $.

  ntp4vc-i1-sint32 $e |- (
    NTP4VCSint32 E
  ) $.

  ntp4vc-a-valid $e |- (
    NTP4VCValidRW F B 1
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      F
      ( NTP4VCShift C 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a-array-separated $e |- (
    NTP4VCSeparated
      B 1
      ( NTP4VCShift C 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a2-array-separated $e |- (
    NTP4VCSeparated
      ( A ` B ) 4
      ( NTP4VCShift C 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN
      F A ( A ` B ) C E D <. 0 , 0 >.
  ) $.

  ntp4vc-a-nodes-separated $e |- A. x e. ZZ
    (
      (
        E <_ x
        /\
        x < ( D + E )
      )
      ->
      (
        NTP4VCSeparated
          B 1
          ( A ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-nodes-array-separated $e |- A. x e. ZZ
    (
      (
        E <_ x
        /\
        x < ( D + E )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C x ) ) 4
          ( NTP4VCShift C 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-nodes-distinct $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        x =/= y
        /\
        (
          E <_ y
          /\
          (
            E <_ x
            /\
            (
              y < ( D + E )
              /\
              x < ( D + E )
            )
          )
        )
      )
      ->
      (
        ( A ` ( NTP4VCShift C x ) )
        =/=
        ( A ` ( NTP4VCShift C y ) )
      )
    ) $.

  ntp4vc-nodes-separated $e |- A. x e. ZZ A. y e. ZZ
    (
      (
        x =/= y
        /\
        (
          E <_ y
          /\
          (
            E <_ x
            /\
            (
              y < ( D + E )
              /\
              x < ( D + E )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C x ) ) 4
          ( A ` ( NTP4VCShift C y ) ) 4
      )
    ) $.

  ntp4vc-swipe-before $e |- (
    NTP4VCSwipeLeft I A C E ( ( D + E ) - 1 )
  ) $.

  ntp4vc-list-pop-more-post-part1-goal14 $a |- (
    NTP4VCSwipeLeft
      (
        NTP4VCUpdate
          I B
          ( A ` ( NTP4VCShift ( A ` B ) 0 ) )
      )
      A C E ( ( D + E ) - 1 )
  ) $.
$}
