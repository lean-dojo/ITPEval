$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_assign_part5_goal28:
  the list-removal pointer assignment satisfies one of the generated alias or
  array-inclusion alternatives under linked-segment, index-search, memory
  validity, integer-bound, distinctness, and separation conditions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCIncluded, NTP4VCSeparated,
  NTP4VCValidRW, NTP4VCInvalid, NTP4VCSint32, and NTP4VCFramed directly
  expand the corresponding source definitions.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate: an
  integer-indexed address function records the finite chain, its array entries,
  writable nodes, and next-pointer steps. NTP4VCUnchanged is the exact
  expansion of the instantiated p_unchanged assumption; because both states
  use the same allocation, pointer, and real-memory maps, all its component
  equalities and its validity implication are retained reflexively.

  NTP4VCIndexOfEq is the total, single-valued graph of l_index_of on the
  nonnegative interval used here: it returns the least matching position, or
  the upper-bound sentinel when there is no match. The class variable P is
  constrained by this graph and is therefore a definitional flattening of the
  source let-bound value x_1, not an additional arbitrary witness. All other
  source let-bound addresses and integers are expanded at every use. The
  arbitrary region function and linked predicate are represented by an
  integer map and a subset of integer maps. The final declaration is
  Metamath's native unproved $a statement encoding; this database adds no $p
  proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCIncluded NTP4VCSeparated NTP4VCValidRW NTP4VCInvalid
  NTP4VCSint32 NTP4VCFramed NTP4VCLinkedN NTP4VCUnchanged
  NTP4VCIndexOfEq
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-included-syntax
  $a wff ( NTP4VCIncluded A B C D ) $.
ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-invalid-syntax
  $a wff ( NTP4VCInvalid A B C ) $.
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

ntp4vc-included-def $a |- ( ( NTP4VCIncluded A B C D ) <->
  (
    0 < B
    ->
    (
      0 <_ D
      /\
      (
        ( NTP4VCBase A ) = ( NTP4VCBase C )
        /\
        (
          ( NTP4VCOffset C ) <_ ( NTP4VCOffset A )
          /\
          (
            ( ( NTP4VCOffset A ) + B )
            <_
            ( ( NTP4VCOffset C ) + D )
          )
        )
      )
    )
  )
) $.

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

ntp4vc-invalid-def $a |- ( ( NTP4VCInvalid A B C ) <->
  (
    0 < C
    ->
    (
      ( A ` ( NTP4VCBase B ) ) <_ ( NTP4VCOffset B )
      \/
      ( ( NTP4VCOffset B ) + C ) <_ 0
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
  $d A B C D E F G H I J K P $.
  $d x y A B C D E F G H I J K P $.

  $( Source parameters:
     A=t_2, B=a_1, C=a, D=i, E=i_1, F=a_2, G=i_2,
     H=t, I=t_1, J=region, K=linked extension, and P=x_1 as the
     uniquely graph-defined l_index_of value. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-a2-address $e |- F e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory $e |- I e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.
  ntp4vc-index-value-integer $e |- P e. ZZ $.

  ntp4vc-index-value $e |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift C 0 ) )
      F E ( D + E ) P
  ) $.

  ntp4vc-a3-not-null $e |- (
    ( A ` B ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a5-not-null $e |- (
    ( A ` ( NTP4VCShift C 0 ) ) =/= <. 0 , 0 >.
  ) $.

  ntp4vc-a5-not-a3 $e |- (
    ( A ` ( NTP4VCShift C 0 ) ) =/= ( A ` B )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ D $.
  ntp4vc-i1-nonnegative $e |- 0 <_ E $.
  ntp4vc-i2-lower-bound $e |- E <_ G $.
  ntp4vc-i2-upper-bound $e |- G <_ ( D + E ) $.

  ntp4vc-region-a1 $e |- (
    ( J ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a2 $e |- (
    ( J ` ( NTP4VCBase F ) ) <_ 0
  ) $.

  ntp4vc-region-a5 $e |- (
    (
      J
      `
      ( NTP4VCBase ( A ` ( NTP4VCShift C 0 ) ) )
    )
    <_
    0
  ) $.

  ntp4vc-i-upper-bound $e |- (
    D <_ ( NTP4VCMaxIndex - 1 )
  ) $.

  ntp4vc-framed-pointer-map $e |- (
    NTP4VCFramed J A
  ) $.

  ntp4vc-linked-allocation $e |- H e. K $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-a1-valid $e |- (
    NTP4VCValidRW H B 1
  ) $.

  ntp4vc-a4-not-invalid $e |- (
    -. ( NTP4VCInvalid H ( NTP4VCShift C 0 ) 1 )
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW H ( NTP4VCShift F 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a1-array-separated $e |- (
    NTP4VCSeparated B 1 ( NTP4VCShift F 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a3-array-separated $e |- (
    NTP4VCSeparated
      ( A ` B ) 4
      ( NTP4VCShift F 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-first-segment $e |- (
    NTP4VCLinkedN
      H A
      ( A ` B )
      F E D
      <. 0 , 0 >.
  ) $.

  ntp4vc-unchanged $e |- (
    NTP4VCUnchanged H A I F E G
  ) $.

  ntp4vc-index-sint32 $e |- (
    NTP4VCSint32 P
  ) $.

  ntp4vc-linked-center-node $e |- (
    NTP4VCLinkedN
      H A C F G 1
      ( A ` ( NTP4VCShift C 0 ) )
  ) $.

  ntp4vc-linked-prefix $e |- (
    NTP4VCLinkedN
      H A
      ( A ` B )
      F E ( G - E ) C
  ) $.

  ntp4vc-linked-suffix $e |- (
    NTP4VCLinkedN
      H A
      ( A ` ( NTP4VCShift C 0 ) )
      F
      ( 1 + G )
      ( ( D + E ) - 1 - G )
      <. 0 , 0 >.
  ) $.

  ntp4vc-no-a5-in-closed-center $e |- A. x e. ZZ
    (
      ( E <_ x /\ x <_ G )
      ->
      (
        ( A ` ( NTP4VCShift F x ) )
        =/=
        ( A ` ( NTP4VCShift C 0 ) )
      )
    ) $.

  ntp4vc-a1-node-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < ( D + E ) )
      ->
      (
        NTP4VCSeparated
          B 1
          ( A ` ( NTP4VCShift F x ) ) 4
      )
    ) $.

  ntp4vc-a5-prefix-node-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < G )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C 0 ) ) 4
          ( A ` ( NTP4VCShift F x ) ) 4
      )
    ) $.

  ntp4vc-node-array-separated $e |- A. x e. ZZ
    (
      ( E <_ x /\ x < ( D + E ) )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift F x ) ) 4
          ( NTP4VCShift F 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-a5-other-node-separated $e |- A. x e. ZZ
    (
      (
        ( A ` ( NTP4VCShift F x ) )
        =/=
        ( A ` ( NTP4VCShift C 0 ) )
        /\
        ( E <_ x /\ x < ( D + E ) )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift C 0 ) ) 4
          ( A ` ( NTP4VCShift F x ) ) 4
      )
    ) $.

  ntp4vc-node-distinct $e |- A. y e. ZZ A. x e. ZZ
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
        ( A ` ( NTP4VCShift F y ) )
        =/=
        ( A ` ( NTP4VCShift F x ) )
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
          ( A ` ( NTP4VCShift F y ) ) 4
          ( A ` ( NTP4VCShift F x ) ) 4
      )
    ) $.

  ntp4vc-list-remove-assign-part5-goal28 $a |- (
    ( NTP4VCShift C 0 ) = B
    \/
    (
      (
        NTP4VCShift
          ( A ` ( NTP4VCShift F ( P - 1 ) ) )
          0
      )
      =
      ( NTP4VCShift C 0 )
      \/
      (
        NTP4VCIncluded
          ( NTP4VCShift C 0 ) 1
          ( NTP4VCShift F P )
          ( ( D + E ) - P )
      )
    )
  ) $.
$}
