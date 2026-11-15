$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_chop_Why3_ide_VClist_chop_more_post_3_part3_goal54:
  the list-chop verification condition preserves a linked-list segment after
  updating one pointer-map entry, under the generated integer bounds,
  memory-validity, framing, allocation-linking, linked-segment, distinctness,
  and separation assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCFramed, and NTP4VCUpdate expand the corresponding
  source definitions. The source let-bound values x, a_2, a_3, a_4, a_5,
  a_6, a_7, x_1, x_2, and m are retained by explicit definitional
  abbreviations.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate. An
  existentially quantified integer-indexed address function records the
  finite chain from the root at position zero to the bound at position n. At
  every integer position in the chain it preserves the array lookup,
  writable-node condition, and next-pointer step, together with the source
  index and length bounds.

  The source region function is an arbitrary integer map, and the source
  linked predicate is an arbitrary subset of integer maps. Every source
  integer quantifier ranges over the full set ZZ with its original
  implication nesting. The final declaration is Metamath's native unproved
  $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCUpdate NTP4VCLinkedN
  NTP4VCX NTP4VCA2 NTP4VCA3 NTP4VCA4 NTP4VCA5
  NTP4VCA6 NTP4VCA7 NTP4VCX1 NTP4VCX2 NTP4VCM
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C D ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-m-class $a class ( NTP4VCM A B C D ) $.

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

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.
ntp4vc-sint-limit-def $a |- NTP4VCSintLimit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A + B ) $.

ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( C ` ( NTP4VCShift D ( NTP4VCX A B ) ) ) $.

ntp4vc-a3-def $a |- ( NTP4VCA3 A B C D ) =
  ( NTP4VCShift ( NTP4VCA2 A B C D ) 0 ) $.

ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D ) =
  ( C ` ( NTP4VCA3 A B C D ) ) $.

ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D ) =
  ( C ` ( NTP4VCShift ( NTP4VCA4 A B C D ) 0 ) ) $.

ntp4vc-a6-def $a |- ( NTP4VCA6 A B ) = ( A ` B ) $.

ntp4vc-a7-def $a |- ( NTP4VCA7 A ) = ( NTP4VCShift A 0 ) $.

ntp4vc-x1-def $a |- ( NTP4VCX1 A ) = ( A - 1 ) $.

ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) = ( A + B ) $.

ntp4vc-m-def $a |- ( NTP4VCM A B C D ) =
  (
    NTP4VCUpdate
      C
      ( NTP4VCA3 A B C D )
      ( NTP4VCA5 A B C D )
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
  $d x y A B C D E F G H I $.

  $( Source parameters:
     A=i_1, B=i_2, C=t_1, D=a_1, E=a, F=i, G=t,
     H=region, I=linked extension. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i2-integer $e |- B e. ZZ $.
  ntp4vc-pointer-map $e |- C e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.

  ntp4vc-a5-null $e |- (
    ( NTP4VCA5 A B C D ) = <. 0 , 0 >.
  ) $.

  ntp4vc-a5-not-a6 $e |- (
    ( NTP4VCA5 A B C D ) =/= ( NTP4VCA6 C E )
  ) $.

  ntp4vc-a5-not-a6-next $e |- (
    ( NTP4VCA5 A B C D )
    =/=
    (
      C
      `
      ( NTP4VCShift ( NTP4VCA6 C E ) 0 )
    )
  ) $.

  ntp4vc-i1-nonnegative $e |- ( 0 <_ A ) $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase E ) ) <_ 0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( H ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-two-le-i $e |- ( 2 <_ F ) $.

  ntp4vc-two-plus-i2-le-i $e |- ( ( 2 + B ) <_ F ) $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed H C ) $.
  ntp4vc-linked-allocation $e |- G e. I $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 A ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 B ) $.

  ntp4vc-a-valid $e |- (
    NTP4VCValidRW G E 1
  ) $.

  ntp4vc-a7-valid $e |- (
    NTP4VCValidRW G ( NTP4VCA7 D ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a-separated-a7 $e |- (
    NTP4VCSeparated E 1 ( NTP4VCA7 D ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a6-separated-a7 $e |- (
    NTP4VCSeparated
      ( NTP4VCA6 C E )
      4
      ( NTP4VCA7 D )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a4-valid $e |- (
    NTP4VCValidRW G ( NTP4VCA4 A B C D ) 4
  ) $.

  ntp4vc-linked-minus-two $e |- (
    NTP4VCLinkedN
      G C
      ( NTP4VCA6 C E )
      D
      A
      ( F - 2 )
      (
        C
        `
        ( NTP4VCShift D ( ( F + A ) - 2 ) )
      )
  ) $.

  ntp4vc-linked-minus-one $e |- (
    NTP4VCLinkedN
      G C
      ( NTP4VCA6 C E )
      D
      A
      ( NTP4VCX1 F )
      (
        C
        `
        ( NTP4VCShift D ( ( F + A ) - 1 ) )
      )
  ) $.

  ntp4vc-linked-main $e |- (
    NTP4VCLinkedN
      G C
      ( NTP4VCA6 C E )
      D
      A F
      ( NTP4VCA5 A B C D )
  ) $.

  ntp4vc-linked-suffix $e |- (
    NTP4VCLinkedN
      G C
      ( NTP4VCA2 A B C D )
      D
      ( NTP4VCX A B )
      ( F - B )
      ( NTP4VCA5 A B C D )
  ) $.

  ntp4vc-a-separated-array $e |- A. x e. ZZ
    (
      A <_ x
      ->
      (
        x < ( NTP4VCX2 F A )
        ->
        (
          NTP4VCSeparated
            E
            1
            ( C ` ( NTP4VCShift D x ) )
            4
        )
      )
    ) $.

  ntp4vc-array-separated-a7 $e |- A. x e. ZZ
    (
      A <_ x
      ->
      (
        x < ( NTP4VCX2 F A )
        ->
        (
          NTP4VCSeparated
            ( C ` ( NTP4VCShift D x ) )
            4
            ( NTP4VCA7 D )
            NTP4VCMaxIndex
        )
      )
    ) $.

  ntp4vc-array-distinct $e |- A. y e. ZZ
    A. x e. ZZ
    (
      y =/= x
      ->
      (
        A <_ x
        ->
        (
          A <_ y
          ->
          (
            x < ( NTP4VCX2 F A )
            ->
            (
              y < ( NTP4VCX2 F A )
              ->
              (
                ( C ` ( NTP4VCShift D y ) )
                =/=
                ( C ` ( NTP4VCShift D x ) )
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-array-separated $e |- A. y e. ZZ
    A. x e. ZZ
    (
      y =/= x
      ->
      (
        A <_ x
        ->
        (
          A <_ y
          ->
          (
            x < ( NTP4VCX2 F A )
            ->
            (
              y < ( NTP4VCX2 F A )
              ->
              (
                NTP4VCSeparated
                  ( C ` ( NTP4VCShift D y ) )
                  4
                  ( C ` ( NTP4VCShift D x ) )
                  4
              )
            )
          )
        )
      )
    ) $.

  ntp4vc-list-chop-more-post-3-part3-goal54
    $a |- (
      NTP4VCLinkedN
        G
        ( NTP4VCM A B C D )
        ( ( NTP4VCM A B C D ) ` E )
        D
        A
        ( NTP4VCX1 F )
        ( NTP4VCA5 A B C D )
    ) $.
$}
