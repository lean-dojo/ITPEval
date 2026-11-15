$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Linked_part2_goal30:
  the list-removal verification condition states that updating the removed
  node's pointer preserves the remaining linked segment, under the generated
  integer bounds, memory validity, framing, linkage, linked-segment,
  index-search, distinctness, and separation assumptions. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCFramed, and NTP4VCUpdate directly expand the
  corresponding source definitions. The source region function is an
  arbitrary integer map, and the source linked predicate is an arbitrary
  subset of integer maps.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  existentially quantified integer-indexed address function records the finite
  chain from the root at position zero to the bound at position n. At every
  integer position in the chain it preserves the array lookup, writable-node
  condition, and next-pointer step, together with the source index and length
  bounds.

  NTP4VCIndexOfEq is the total, single-valued graph of l_index_of: it returns
  the first matching integer position in the searched half-open interval, or
  the upper-bound sentinel if no position matches. The class variable P is
  constrained by that graph and names exactly the source index-search result.
  Every source let-bound value is expanded at each use, every source integer
  quantifier ranges over the full set ZZ, and NTP4VCUpdate is functional
  update on the full address domain. The final declaration is Metamath's
  native unproved $a statement encoding; this database adds no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCUpdate NTP4VCLinkedN NTP4VCIndexOfEq
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
  $d A B C D E F H I J K P $.
  $d x y A B C D E F H I J K P $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, D=i_2, E=i, F=i_1, H=t,
     I=region, J=linked extension, K=t_2, and P=l_index_of result. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-result-pointer-map $e |- K e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-result-integer $e |- P e. ZZ $.

  ntp4vc-a2-nonnull $e |- (
    ( A ` B ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a3-nonnull $e |- (
    ( A ` ( NTP4VCShift C D ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a3-equals-a2 $e |- (
    ( A ` ( NTP4VCShift C D ) ) = ( A ` B )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-le-i2 $e |- F <_ D $.
  ntp4vc-i2-lt-x $e |- D < ( E + F ) $.

  ntp4vc-region-a $e |- (
    ( I ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( I ` ( NTP4VCBase C ) ) <_ 0
  ) $.

  ntp4vc-region-a2 $e |- (
    ( I ` ( NTP4VCBase ( A ` B ) ) ) <_ 0
  ) $.

  ntp4vc-i-upper-bound $e |- (
    E <_ ( NTP4VCMaxIndex - 1 )
  ) $.

  ntp4vc-framed-pointer-map $e |- (
    NTP4VCFramed I A
  ) $.

  ntp4vc-linked-allocation $e |- H e. J $.

  ntp4vc-i-sint32 $e |- (
    NTP4VCSint32 E
  ) $.

  ntp4vc-i1-sint32 $e |- (
    NTP4VCSint32 F
  ) $.

  ntp4vc-a-valid $e |- (
    NTP4VCValidRW H B 1
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      H
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
      H A ( A ` B ) C F E <. 0 , 0 >.
  ) $.

  ntp4vc-index-of-graph $e |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift C D ) )
      C F ( E + F ) P
  ) $.

  ntp4vc-index-sint32 $e |- (
    NTP4VCSint32 P
  ) $.

  ntp4vc-a-nodes-separated $e |- A. x e. ZZ
    (
      ( F <_ x /\ x < ( E + F ) )
      ->
      (
        NTP4VCSeparated
          B 1
          ( A ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-nodes-array-separated $e |- A. x e. ZZ
    (
      ( F <_ x /\ x < ( E + F ) )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C x ) ) 4
          ( NTP4VCShift C 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-a3-other-node-separated $e |- A. x e. ZZ
    (
      (
        ( A ` ( NTP4VCShift C D ) )
        =/=
        ( A ` ( NTP4VCShift C x ) )
        /\
        ( F <_ x /\ x < ( E + F ) )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C D ) ) 4
          ( A ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-nodes-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          F <_ x
          /\
          (
            F <_ y
            /\
            (
              x < ( E + F )
              /\
              y < ( E + F )
            )
          )
        )
      )
      ->
      (
        ( A ` ( NTP4VCShift C y ) )
        =/=
        ( A ` ( NTP4VCShift C x ) )
      )
    ) $.

  ntp4vc-node-pairs-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          F <_ x
          /\
          (
            F <_ y
            /\
            (
              x < ( E + F )
              /\
              y < ( E + F )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C y ) ) 4
          ( A ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-result-linked-before-update $e |- (
    NTP4VCLinkedN
      H K
      ( A ` ( NTP4VCShift ( A ` B ) 0 ) )
      C F ( E - 1 ) <. 0 , 0 >.
  ) $.

  ntp4vc-a-result-nodes-separated $e |- A. x e. ZZ
    (
      ( F <_ x /\ x < ( ( E + F ) - 1 ) )
      ->
      (
        NTP4VCSeparated
          B 1
          ( K ` ( NTP4VCShift C x ) ) 4
      )
    ) $.

  ntp4vc-list-remove-contains-item-post-linked-part2-goal30 $a |- (
    NTP4VCLinkedN
      H
      (
        NTP4VCUpdate
          K B
          ( A ` ( NTP4VCShift ( A ` B ) 0 ) )
      )
      ( A ` ( NTP4VCShift ( A ` B ) 0 ) )
      C F ( E - 1 ) <. 0 , 0 >.
  ) $.
$}
