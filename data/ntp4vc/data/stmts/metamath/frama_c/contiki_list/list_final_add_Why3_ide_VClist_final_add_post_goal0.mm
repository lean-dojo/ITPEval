$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/list_final_add_Why3_ide_VClist_final_add_post_goal0:
  the final-add verification condition preserves a linked-list segment after
  two pointer-map updates, under the generated integer bounds, memory
  validity, framing, allocation-linking, distinctness, and separation
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCValidRW,
  NTP4VCSint32, and NTP4VCFramed expand the corresponding source definitions.
  NTP4VCUpdate is full-domain functional update. NTP4VCX is the source
  let-bound integer x, and NTP4VCM is the source let-bound pointer map m with
  its two updates retained in order. The source's remaining let-bound
  addresses are displayed directly in the hypotheses and conclusion.

  NTP4VCLinkedN is equivalent to the source inductive p_linked_n predicate:
  an integer-indexed address function records the finite pointer chain from
  its root to its bound, together with every constructor bound, array lookup,
  writable-node condition, and next-pointer step. All integer quantifiers
  range over the full set ZZ, and every address and function ranges over its
  full source domain.

  The arbitrary integer-valued map I represents the source region function,
  and membership of the allocation map H in the arbitrary set J represents
  the source linked predicate. The final declaration is Metamath's native
  unproved $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSintLimit
  NTP4VCSeparated NTP4VCValidRW NTP4VCSint32 NTP4VCFramed
  NTP4VCUpdate NTP4VCX NTP4VCM NTP4VCLinkedN
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint-limit-class $a class NTP4VCSintLimit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-m-class $a class ( NTP4VCM A B C D E F ) $.

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

ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A + B ) $.

ntp4vc-m-def $a |- ( NTP4VCM A B C D E F ) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          A
          ( NTP4VCShift E ( NTP4VCX C D ) )
          B
      )
      ( NTP4VCShift F 0 )
      B
  ) $.

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
                    (
                      0 <_ x
                      /\
                      x < Q
                    )
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
                          (
                            B
                            `
                            ( NTP4VCShift ( f ` x ) 0 )
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
    )
  ) $.
$}

${
  $d A B C D E F G H I J $.

  $( Source parameters:
     A=t_1, B=a_1, C=i, D=i_1, E=a_3, F=a, G=a_2, H=t,
     I=region, J=linked extension. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-a3-address $e |- E e. NTP4VCAddr $.
  ntp4vc-a-address $e |- F e. NTP4VCAddr $.
  ntp4vc-a2-address $e |- G e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.

  ntp4vc-a4-null $e |- (
    ( A ` ( NTP4VCShift B 0 ) ) = <. 0 , 0 >.
  ) $.

  ntp4vc-x-positive $e |- 0 < ( NTP4VCX C D ) $.

  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase F ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( I ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a2 $e |- ( I ` ( NTP4VCBase G ) ) <_ 0 $.
  ntp4vc-region-a3 $e |- ( I ` ( NTP4VCBase E ) ) <_ 0 $.

  ntp4vc-x-upper-bound $e |- (
    ( NTP4VCX C D ) <_ ( NTP4VCMaxIndex - 1 )
  ) $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed I A ) $.
  ntp4vc-linked-allocation $e |- H e. J $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 D ) $.

  ntp4vc-a-valid $e |- ( NTP4VCValidRW H F 1 ) $.
  ntp4vc-a1-valid $e |- ( NTP4VCValidRW H B 4 ) $.
  ntp4vc-a2-valid $e |- ( NTP4VCValidRW H G 4 ) $.

  ntp4vc-a-a1-separated $e |- (
    NTP4VCSeparated F 1 B 4
  ) $.

  ntp4vc-a-a2-separated $e |- (
    NTP4VCSeparated F 1 G 4
  ) $.

  ntp4vc-a2-a1-separated $e |- (
    NTP4VCSeparated G 4 B 4
  ) $.

  ntp4vc-array-valid $e |- (
    NTP4VCValidRW
      H
      ( NTP4VCShift E 0 )
      NTP4VCMaxIndex
  ) $.

  ntp4vc-a-array-separated $e |- (
    NTP4VCSeparated
      F 1
      ( NTP4VCShift E 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a1-array-separated $e |- (
    NTP4VCSeparated
      B 4
      ( NTP4VCShift E 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-a6-array-separated $e |- (
    NTP4VCSeparated
      ( A ` F ) 4
      ( NTP4VCShift E 0 ) NTP4VCMaxIndex
  ) $.

  ntp4vc-linked-prefix $e |- (
    NTP4VCLinkedN
      H A ( A ` F ) E D ( C - 1 ) G
  ) $.

  ntp4vc-linked-singleton $e |- (
    NTP4VCLinkedN
      H A G E ( ( NTP4VCX C D ) - 1 ) 1
      ( A ` ( NTP4VCShift G 0 ) )
  ) $.

  ntp4vc-a-node-separated $e |- A. x e. ZZ
    (
      ( D <_ x /\ x < ( NTP4VCX C D ) )
      ->
      (
        NTP4VCSeparated
          F 1
          ( A ` ( NTP4VCShift E x ) ) 4
      )
    ) $.

  ntp4vc-a1-node-separated $e |- A. x e. ZZ
    (
      ( D <_ x /\ x < ( NTP4VCX C D ) )
      ->
      (
        NTP4VCSeparated
          B 4
          ( A ` ( NTP4VCShift E x ) ) 4
      )
    ) $.

  ntp4vc-node-array-separated $e |- A. x e. ZZ
    (
      ( D <_ x /\ x < ( NTP4VCX C D ) )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift E x ) ) 4
          ( NTP4VCShift E 0 ) NTP4VCMaxIndex
      )
    ) $.

  ntp4vc-node-distinct $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          D <_ x
          /\
          (
            D <_ y
            /\
            (
              x < ( NTP4VCX C D )
              /\
              y < ( NTP4VCX C D )
            )
          )
        )
      )
      ->
      (
        ( A ` ( NTP4VCShift E y ) )
        =/=
        ( A ` ( NTP4VCShift E x ) )
      )
    ) $.

  ntp4vc-node-pair-separated $e |- A. y e. ZZ A. x e. ZZ
    (
      (
        y =/= x
        /\
        (
          D <_ x
          /\
          (
            D <_ y
            /\
            (
              x < ( NTP4VCX C D )
              /\
              y < ( NTP4VCX C D )
            )
          )
        )
      )
      ->
      (
        NTP4VCSeparated
          ( A ` ( NTP4VCShift E y ) ) 4
          ( A ` ( NTP4VCShift E x ) ) 4
      )
    ) $.

  ntp4vc-list-final-add-post-goal0 $a |- (
    NTP4VCLinkedN
      H
      ( NTP4VCM A B C D E G )
      ( ( NTP4VCM A B C D E G ) ` F )
      E D ( 1 + C )
      ( A ` ( NTP4VCShift B 0 ) )
  ) $.
$}
