$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19:
  the strncpy not-exceed postcondition concludes that the destination at a_1
  is a valid bounded string for the offset difference, under the generated
  havoc, address-order, string-validity, bounded-string-validity,
  memory-validity, copied-prefix, linking, constancy, region, and unsigned-
  range assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCSint8, NTP4VCUint64, NTP4VCValidStr, and NTP4VCValidStrn directly
  expand the corresponding source definitions. NTP4VCHavoc is fixed
  pointwise by havoc_access.

  The arbitrary integer-valued map I represents region. Membership of the
  allocation map G in the arbitrary set J represents linked, while membership
  of the memory E in the arbitrary set K represents sconst. The arbitrary
  relation L represents addr_le, with its source law under equal bases
  retained explicitly. M represents to_uint64, while N and O represent
  l_strlen and l_strnlen. Their exact range, identity, and fixed-point laws
  retain the relevant imported source theory without assigning stronger
  properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  maps, relations, predicates, and quantified indices keep their original
  unrestricted domains. The existential null-position witnesses in
  NTP4VCValidStr and NTP4VCValidStrn remain internally quantified over all
  integers, and the copied-prefix assumption retains its full integer
  quantifier and implication scope. Splitting the source implication chain
  into scoped essential hypotheses is bidirectionally equivalent to the
  original statement. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSeparated
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr NTP4VCValidStrn
  NTP4VCHavoc NTP4VCStrlen NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.
ntp4vc-valid-strn-syntax $a wff ( NTP4VCValidStrn A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.
ntp4vc-strnlen-def $a |- ( NTP4VCStrnlen A B C D ) =
  ( A ` <. <. B , C >. , D >. ) $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A
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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

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
  $d x y A B C $.
  ntp4vc-valid-str-def $a |- ( ( NTP4VCValidStr A B C ) <->
    E. x e. ZZ
      (
        ( B ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          ( NTP4VCUint64 x )
          /\
          (
            ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + x ) )
            /\
            A. y e. ZZ
              (
                y <_ x
                ->
                ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
              )
          )
        )
      )
  ) $.
$}

${
  $d x y A B C D $.
  ntp4vc-valid-strn-def $a |- ( ( NTP4VCValidStrn A B C D ) <->
    (
      ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + D ) )
      \/
      (
        E. x e. ZZ
          (
            ( B ` ( NTP4VCShift C x ) ) = 0
            /\
            (
              x < D
              /\
              (
                ( NTP4VCUint64 x )
                /\
                (
                  NTP4VCValidRW
                    A
                    ( NTP4VCShift C 0 )
                    ( 1 + x )
                )
              )
            )
          )
        /\
        A. y e. ZZ
          (
            y <_ D
            ->
            ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
          )
      )
    )
  ) $.
$}

${
  $d x y z A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=a_3, B=a_1, C=a, D=t_1, E=t_2, F=t_3, G=t, and H=a_2.
     I is region; J and K are the linked and sconst extensions; L is the
     addr_le extension; M is to_uint64; N is l_strlen; and O is l_strnlen.
     Source lets are expanded as:
       x=base(A), x_1=base(B), a_4=shift(B,0),
       x_2=offset(B), x_3=offset(C), and x_4=offset(C)-offset(B). $)

  ntp4vc-a3-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-a2-address $e |- H e. NTP4VCAddr $.

  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- K C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- L C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint64-function $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- N e.
    (
      ZZ
      ^m
      ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr )
    ) $.
  ntp4vc-strnlen-function $e |- O e.
    (
      ZZ
      ^m
      ( ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) X. ZZ )
    ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe L x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( M ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( M ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen N x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( M ` ( 1 + ( NTP4VCStrlen N x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen N x y ) ) $.

  ntp4vc-strnlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrnlen O x y z )
            =
            if
            (
              (
                z = 0
                \/
                ( x ` ( NTP4VCShift y 0 ) ) = 0
              ) ,
              0 ,
              (
                M
                `
                (
                  1
                  +
                  (
                    NTP4VCStrnlen
                      O
                      x
                      ( NTP4VCShift y 1 )
                      ( M ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-strnlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCStrnlen O x y z ) ) $.

  ntp4vc-distinct-bases $e |- (
    ( NTP4VCBase A ) =/= ( NTP4VCBase B )
  ) $.

  ntp4vc-havoc-result $e |- (
    (
      NTP4VCHavoc
        D E
        ( NTP4VCShift B 0 )
        ( 1 + ( NTP4VCStrnlen O F A 0 ) )
    )
    =
    F
  ) $.

  ntp4vc-a1-offset-le-a-offset $e |- (
    ( NTP4VCOffset B ) <_ ( NTP4VCOffset C )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( I ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-a3 $e |- (
    ( I ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-a-offset-before-source-end $e |- (
    ( NTP4VCOffset C )
    <
    (
      ( NTP4VCOffset B )
      +
      ( NTP4VCStrlen N E A )
    )
  ) $.

  ntp4vc-linked-allocation $e |- G e. J $.
  ntp4vc-sconst-t2 $e |- E e. K $.

  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe L B C ) $.
  ntp4vc-a3-le-a2 $e |- ( NTP4VCAddrLe L A H ) $.

  ntp4vc-a3-valid-string-t2 $e |- (
    NTP4VCValidStr G E A
  ) $.

  ntp4vc-a2-valid-string-t3 $e |- (
    NTP4VCValidStr G F H
  ) $.

  ntp4vc-offset-difference-uint64 $e |- (
    NTP4VCUint64
      ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-a3-valid-bounded-string-t2 $e |- (
    NTP4VCValidStrn
      G E A
      ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-a-valid-bounded-string-t3 $e |- (
    NTP4VCValidStrn
      G F C
      ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-a-le-a1-offset-end $e |- (
    NTP4VCAddrLe
      L
      C
      (
        NTP4VCShift
          B
          ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
      )
  ) $.

  ntp4vc-a2-le-a3-bounded-end $e |- (
    NTP4VCAddrLe
      L
      H
      (
        NTP4VCShift
          A
          (
            NTP4VCStrnlen
              O F A
              ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
          )
      )
  ) $.

  ntp4vc-a1-bounded-region-valid-rw $e |- (
    NTP4VCValidRW
      G
      ( NTP4VCShift B 0 )
      (
        1
        +
        (
          NTP4VCStrnlen
            O E A
            ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
        )
      )
  ) $.

  ntp4vc-copied-prefix $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + ( NTP4VCOffset A ) ) < ( NTP4VCOffset H )
        ->
        (
          ( F ` ( NTP4VCShift A x ) )
          =
          ( F ` ( NTP4VCShift B x ) )
        )
      )
    ) $.

  ntp4vc-strncpy-not-exceed-post-2-goal19 $a |- (
    NTP4VCValidStrn
      G F B
      ( ( NTP4VCOffset C ) - ( NTP4VCOffset B ) )
  ) $.
$}
