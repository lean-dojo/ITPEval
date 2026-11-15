$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_6_preserved_goal12:
  the strncmp loop-invariant preservation condition concludes the one-step
  bounded-string length and address-offset identity for the third current
  string position after consuming one byte, under the generated
  byte-conversion, offset-alignment, prefix-equality, address-order,
  memory-validity, linking, constancy, and exact integer-range assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint8, NTP4VCUint64, and NTP4VCValidStrn directly expand the
  corresponding source definitions.

  The arbitrary relation K represents addr_le, with its source law under
  equal bases retained explicitly. The arbitrary map H and sets I and J
  represent region, linked, and sconst. L and M represent to_uint8 and
  to_uint64, while N represents l_strnlen. Their source range, identity, and
  fixed-point laws are retained as explicit hypotheses without assigning
  stronger properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  functions, relations, and predicates retain their unrestricted source
  domains. The existential null-position witnesses in all four bounded-string
  assumptions remain internal, and both prefix assumptions retain their full
  integer quantifiers and implication scopes. Proposition equality in the
  second prefix assumption is rendered by the equivalent biconditional.
  Splitting the source implication chain into scoped essential hypotheses is
  bidirectionally equivalent to the original statement. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no translation-specific $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint8 NTP4VCUint64 NTP4VCValidStrn
  NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint8-limit-class $a class NTP4VCUint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint8-syntax $a wff ( NTP4VCUint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-strn-syntax $a wff ( NTP4VCValidStrn A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint8-limit-def $a |- NTP4VCUint8Limit = ; ; 2 5 6 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint8-def $a |- ( ( NTP4VCUint8 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint8Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

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
  $d x y z A B C D E F G H I J K L M N $.

  $( Source parameters:
     A=t_1, B=a_2, C=a_3, D=a_1, E=a, F=i, and G=t.
     H is region; I and J are the linked and sconst extensions; K is the
     addr_le extension; L and M are to_uint8 and to_uint64; and N is
     l_strnlen. Source lets are expanded as:
       x=A(B), x_1=L(A(B)), x_2=A(C), x_3=offset(D), x_4=offset(C),
       x_5=offset(E), x_6=offset(B), x_7=offset(C)-offset(E),
       x_8=A(shift(D,x_7)), x_9=A(shift(E,x_7)),
       x_10=F+offset(B)-offset(D), x_11=strnlen(A,E,x_10),
       x_12=offset(E)+x_11, and x_13=strnlen(A,D,x_10). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a2-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a3-address $e |- C e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- K C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint8-function $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint64-function $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-strnlen-function $e |- N e.
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
        ( NTP4VCAddrLe K x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint8-range $e |- A. x e. ZZ
    ( NTP4VCUint8 ( L ` x ) ) $.

  ntp4vc-to-uint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint8 x )
      ->
      ( L ` x ) = x
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( M ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( M ` x ) = x
    ) $.

  ntp4vc-strnlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrnlen N x y z )
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
                      N
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
          ( NTP4VCUint64 ( NTP4VCStrnlen N x y z ) ) $.

  ntp4vc-i-nonzero $e |- F =/= 0 $.

  ntp4vc-a2-byte-nonzero $e |- (
    ( L ` ( A ` B ) ) =/= 0
  ) $.

  ntp4vc-current-byte-conversions-equal $e |- (
    ( L ` ( A ` C ) ) = ( L ` ( A ` B ) )
  ) $.

  ntp4vc-offset-balance $e |- (
    ( ( NTP4VCOffset D ) + ( NTP4VCOffset C ) )
    =
    ( ( NTP4VCOffset E ) + ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-aligned-memory-values-equal $e |- (
    (
      A
      `
      (
        NTP4VCShift
          D
          ( ( NTP4VCOffset C ) - ( NTP4VCOffset E ) )
      )
    )
    =
    (
      A
      `
      (
        NTP4VCShift
          E
          ( ( NTP4VCOffset C ) - ( NTP4VCOffset E ) )
      )
    )
  ) $.

  ntp4vc-a-length-alignment $e |- (
    (
      ( NTP4VCOffset E )
      +
      (
        NTP4VCStrnlen
          N A E
          ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
      )
    )
    =
    (
      ( NTP4VCOffset C )
      +
      ( NTP4VCStrnlen N A C F )
    )
  ) $.

  ntp4vc-a1-length-alignment $e |- (
    (
      ( NTP4VCOffset D )
      +
      (
        NTP4VCStrnlen
          N A D
          ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
      )
    )
    =
    (
      ( NTP4VCOffset B )
      +
      ( NTP4VCStrnlen N A B F )
    )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ F $.

  ntp4vc-a1-offset-le-a2-offset $e |- (
    ( NTP4VCOffset D ) <_ ( NTP4VCOffset B )
  ) $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase E ) ) <_ 0
  ) $.

  ntp4vc-region-a1 $e |- (
    ( H ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- G e. I $.
  ntp4vc-sconst-memory $e |- A e. J $.
  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 F ) $.
  ntp4vc-a-le-a3 $e |- ( NTP4VCAddrLe K E C ) $.
  ntp4vc-a1-le-a2 $e |- ( NTP4VCAddrLe K D B ) $.
  ntp4vc-a2-value-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a3-value-sint8 $e |- ( NTP4VCSint8 ( A ` C ) ) $.

  ntp4vc-a2-valid-bounded-string $e |- (
    NTP4VCValidStrn G A B F
  ) $.

  ntp4vc-a3-valid-bounded-string $e |- (
    NTP4VCValidStrn G A C F
  ) $.

  ntp4vc-remaining-count-uint64 $e |- (
    NTP4VCUint64
      ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-a-aligned-value-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        (
          NTP4VCShift
            E
            ( ( NTP4VCOffset C ) - ( NTP4VCOffset E ) )
        )
      )
  ) $.

  ntp4vc-a1-aligned-value-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        (
          NTP4VCShift
            D
            ( ( NTP4VCOffset C ) - ( NTP4VCOffset E ) )
        )
      )
  ) $.

  ntp4vc-a-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      G A E
      ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-a1-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      G A D
      ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-a2-le-a1-end $e |- (
    NTP4VCAddrLe
      K
      B
      (
        NTP4VCShift
          D
          (
            NTP4VCStrnlen
              N A D
              ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
          )
      )
  ) $.

  ntp4vc-a3-le-a-end $e |- (
    NTP4VCAddrLe
      K
      C
      (
        NTP4VCShift
          E
          (
            NTP4VCStrnlen
              N A E
              ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
          )
      )
  ) $.

  ntp4vc-prefix-equality-through-a2-offset $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + ( NTP4VCOffset D ) ) < ( NTP4VCOffset B )
        ->
        (
          ( A ` ( NTP4VCShift D x ) )
          =
          ( A ` ( NTP4VCShift E x ) )
        )
      )
    ) $.

  ntp4vc-byte-conversion-reflects-equality $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x
        <
        (
          NTP4VCStrnlen
            N A E
            ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
        )
        ->
        (
          (
            ( L ` ( A ` ( NTP4VCShift D x ) ) )
            =
            ( L ` ( A ` ( NTP4VCShift E x ) ) )
          )
          <->
          (
            ( A ` ( NTP4VCShift D x ) )
            =
            ( A ` ( NTP4VCShift E x ) )
          )
        )
      )
    ) $.

  ntp4vc-strncmp-loop-inv-6-preserved-goal12 $a |- (
    (
      ( NTP4VCOffset E )
      +
      (
        NTP4VCStrnlen
          N A E
          ( ( F + ( NTP4VCOffset B ) ) - ( NTP4VCOffset D ) )
      )
    )
    =
    (
      ( 1 + ( NTP4VCOffset C ) )
      +
      (
        NTP4VCStrnlen
          N A
          ( NTP4VCShift C 1 )
          ( M ` ( F - 1 ) )
      )
    )
  ) $.
$}
