$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Unchanged_part5_goal60:
  the list-removal verification condition states that updating the removed
  node's next pointer preserves the list structures and writable validity
  throughout the prefix whose exclusive upper bound is one less than the
  found-item index, under the generated integer bounds, memory validity,
  framing, linkage, linked-segment, unchanged-state, index-search,
  distinctness, and separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented by ZZ X. ZZ, with their base and offset given by
  1st and 2nd. The shift, separation, writable-validity, signed-32-bit,
  framing, and full-domain functional-update operations directly expand their
  source definitions.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate: an
  existentially quantified integer-indexed address function records the finite
  chain, its array entries, writable nodes, and next-pointer steps.
  NTP4VCUnchanged directly expands p_unchanged for a shared allocation map
  and real-memory map and two possibly different pointer maps, retaining the
  array-entry equality, pointer field, all three real fields, and writable
  validity implication. Thus the hypothesis is its reflexive same-state
  instance and the conclusion compares the updated pointer map with the
  original map exactly as in the source.

  NTP4VCIndexOfEq is the total, single-valued graph of l_index_of: it returns
  the first matching integer position in the searched half-open interval, or
  the upper-bound sentinel when no position matches. P is constrained by that
  graph and names exactly the source index-search result. Every source
  let-bound value is expanded at each use, every integer quantifier ranges over
  all of ZZ, and NTP4VCUpdate is functional update on the full address domain.
  The arbitrary source region function and linked predicate are retained as an
  integer map and a subset of integer maps. The final declaration is
  Metamath's native unproved $a statement encoding; this database adds no $p
  proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCUpdate NTP4VCLinkedN NTP4VCUnchanged NTP4VCIndexOfEq
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
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E P Q ) $.
ntp4vc-index-of-eq-syntax
  $a wff ( NTP4VCIndexOfEq A B C D E F ) $.

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
  $d x A B C D E P Q $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D E P Q )
    <->
    A. x e. ZZ
    (
      ( P <_ x /\ x < Q )
      ->
      (
        ( B ` ( NTP4VCShift E x ) )
        =
        ( C ` ( NTP4VCShift E x ) )
        /\
        (
          (
            B
            `
            (
              NTP4VCShift
              ( B ` ( NTP4VCShift E x ) )
              0
            )
          )
          =
          (
            C
            `
            (
              NTP4VCShift
              ( C ` ( NTP4VCShift E x ) )
              0
            )
          )
          /\
          (
            (
              D
              `
              (
                NTP4VCShift
                ( B ` ( NTP4VCShift E x ) )
                1
              )
            )
            =
            (
              D
              `
              (
                NTP4VCShift
                ( C ` ( NTP4VCShift E x ) )
                1
              )
            )
            /\
            (
              (
                D
                `
                (
                  NTP4VCShift
                  ( B ` ( NTP4VCShift E x ) )
                  2
                )
              )
              =
              (
                D
                `
                (
                  NTP4VCShift
                  ( C ` ( NTP4VCShift E x ) )
                  2
                )
              )
              /\
              (
                (
                  D
                  `
                  (
                    NTP4VCShift
                    ( B ` ( NTP4VCShift E x ) )
                    3
                  )
                )
                =
                (
                  D
                  `
                  (
                    NTP4VCShift
                    ( C ` ( NTP4VCShift E x ) )
                    3
                  )
                )
                /\
                (
                  ( NTP4VCValidRW A ( C ` ( NTP4VCShift E x ) ) 4 )
                  ->
                  ( NTP4VCValidRW A ( B ` ( NTP4VCShift E x ) ) 4 )
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
  $d A B C D E F G H J K L M P $.
  $d x y A B C D E F G H J K L M P $.

  $( Source parameters:
     A=t_2, B=a_1, C=a, D=a_2, E=i_2, F=i, G=i_1, H=i_3,
     J=t, K=t_1, L=region, M=linked extension, and
     P=l_index_of result. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-i3-integer $e |- H e. ZZ $.
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

  ntp4vc-i-upper-bound $e |- (
    F <_ ( NTP4VCMaxIndex - 1 )
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
    NTP4VCUnchanged J A A K D G H
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

  ntp4vc-list-remove-contains-item-post-unchanged-part5-goal60
    $a |- (
      NTP4VCUnchanged
        J
        (
          NTP4VCUpdate
            A
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
        A K D G ( P - 1 )
    ) $.
$}
