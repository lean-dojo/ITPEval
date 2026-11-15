$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_loop_inv_2_preserved_goal8:
  the list-remove loop invariant preserves a linked-list segment after
  extending its length by one, under the generated integer bounds, memory
  validity, framing, linkage, unchanged-state, index-search, distinctness,
  and separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, and NTP4VCFramed directly expand the corresponding source
  definitions. The arbitrary integer map K is the source region function, and
  membership of the allocation map I in the arbitrary set L is the source
  linked predicate.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  internally existential integer-indexed address function records the finite
  chain from its root to its bound, including every array lookup,
  writable-node condition, and next-pointer step. NTP4VCUnchanged is the exact
  instantiated p_unchanged condition; the two source states have identical
  allocation, pointer, and real-memory maps, so all field equalities and the
  validity implication are retained reflexively.

  NTP4VCIndexOfEq is the total, single-valued graph of l_index_of: it returns
  the first matching position in the searched half-open integer interval, or
  its upper endpoint when no position matches. P is constrained by this graph
  and therefore denotes exactly the source function value. Source let-bound
  values are expanded at every use, and all integer quantifiers range over
  the full set ZZ. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCLinkedN NTP4VCUnchanged NTP4VCIndexOfEq
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

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
  $d A B C D E F G H I J K L P $.
  $d f x y A B C D E F G H I J K L P $.

  $( Source parameters:
     A=t_2, B=a_1, C=a, D=i, E=i_1, F=i_2, G=a_3, H=a_2,
     I=t, J=t_1, K=region, L=linked extension, and
     P=l_index_of result. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-a3-address $e |- G e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- H e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory-map $e |- J e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-result-integer $e |- P e. ZZ $.

  ntp4vc-a2-nonnull $e |- H =/= <. 0 , 0 >. $.

  ntp4vc-a4-not-a2 $e |- (
    ( A ` B ) =/= H
  ) $.

  ntp4vc-a4-nonnull $e |- (
    ( A ` B ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a5-not-a2 $e |- (
    ( A ` ( NTP4VCShift C 0 ) ) =/= H
  ) $.

  ntp4vc-a5-nonnull $e |- (
    ( A ` ( NTP4VCShift C 0 ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ D $.
  ntp4vc-i1-nonnegative $e |- 0 <_ E $.
  ntp4vc-i1-le-i2 $e |- E <_ F $.
  ntp4vc-i2-le-x $e |- F <_ ( D + E ) $.

  ntp4vc-region-a1 $e |- (
    ( K ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a2 $e |- (
    ( K ` ( NTP4VCBase H ) ) <_ 0
  ) $.

  ntp4vc-region-a3 $e |- (
    ( K ` ( NTP4VCBase G ) ) <_ 0
  ) $.

  ntp4vc-i-upper-bound $e |- (
    D <_ ( NTP4VCMaxIndex - 1 )
  ) $.

  ntp4vc-framed-pointer-map $e |- (
    NTP4VCFramed K A
  ) $.

  ntp4vc-linked-allocation $e |- I e. L $.

  ntp4vc-i-sint32 $e |- (
    NTP4VCSint32 D
  ) $.

  ntp4vc-i1-sint32 $e |- (
    NTP4VCSint32 E
  ) $.

  ntp4vc-i2-sint32 $e |- (
    NTP4VCSint32 F
  ) $.

  ntp4vc-a1-valid $e |- (
    NTP4VCValidRW I B 1
  ) $.

  ntp4vc-one-plus-i2-sint32 $e |- (
    NTP4VCSint32 ( 1 + F )
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      I
      ( NTP4VCShift G 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a1-array-separated $e |- (
    NTP4VCSeparated
      B 1
      ( NTP4VCShift G 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a4-array-separated $e |- (
    NTP4VCSeparated
      ( A ` B ) 4
      ( NTP4VCShift G 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-before $e |- (
    NTP4VCLinkedN
      I A ( A ` B ) G E D <. 0 , 0 >.
  ) $.

  ntp4vc-unchanged $e |- (
    NTP4VCUnchanged I A J G E F
  ) $.

  ntp4vc-index-of-graph $e |- (
    NTP4VCIndexOfEq
      A H G E ( D + E ) P
  ) $.

  ntp4vc-index-sint32 $e |- (
    NTP4VCSint32 P
  ) $.

  ntp4vc-single-node-linked $e |- (
    NTP4VCLinkedN
      I A C G F 1
      ( A ` ( NTP4VCShift C 0 ) )
  ) $.

  ntp4vc-prefix-linked $e |- (
    NTP4VCLinkedN
      I A ( A ` B ) G E ( F - E ) C
  ) $.

  ntp4vc-suffix-linked $e |- (
    NTP4VCLinkedN
      I A
      ( A ` ( NTP4VCShift C 0 ) )
      G
      ( 1 + F )
      ( ( ( D + E ) - 1 ) - F )
      <. 0 , 0 >.
  ) $.

  ntp4vc-item-not-in-prefix $e |- A. x e. ZZ
    (
      ( E <_ x /\ x <_ F )
      ->
      ( A ` ( NTP4VCShift G x ) ) =/= H
    ) $.

  ntp4vc-a1-nodes-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < ( D + E ) )
      ->
      (
        NTP4VCSeparated
          B 1
          ( A ` ( NTP4VCShift G x ) ) 4
      )
    ) $.

  ntp4vc-a2-prefix-nodes-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < F )
      ->
      (
        NTP4VCSeparated
          H 4
          ( A ` ( NTP4VCShift G x ) ) 4
      )
    ) $.

  ntp4vc-nodes-array-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < ( D + E ) )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift G x ) ) 4
          ( NTP4VCShift G 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-a2-other-node-separated $e |- A. x e. ZZ
    (
      (
        ( A ` ( NTP4VCShift G x ) ) =/= H
        /\
        ( E <_ x /\ x < ( D + E ) )
      )
      ->
      (
        NTP4VCSeparated
          H 4
          ( A ` ( NTP4VCShift G x ) ) 4
      )
    ) $.

  ntp4vc-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          E <_ x
          /\
          (
            E <_ y
            /\
            (
              x < ( D + E )
              /\
              y < ( D + E )
            )
          )
        )
      )
      ->
      (
        ( A ` ( NTP4VCShift G y ) )
        =/=
        ( A ` ( NTP4VCShift G x ) )
      )
    ) $.

  ntp4vc-node-pairs-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          E <_ x
          /\
          (
            E <_ y
            /\
            (
              x < ( D + E )
              /\
              y < ( D + E )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift G y ) ) 4
          ( A ` ( NTP4VCShift G x ) ) 4
      )
    ) $.

  ntp4vc-list-remove-loop-inv-2-preserved-goal8 $a |- (
    NTP4VCLinkedN
      I A ( A ` B ) G E
      ( ( 1 + F ) - E )
      ( A ` ( NTP4VCShift C 0 ) )
  ) $.
$}
