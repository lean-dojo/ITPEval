$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strnchr_Why3_ide_VCstrnchr_loop_inv_4_preserved_goal5:
  the strnchr loop-invariant preservation condition concludes that advancing
  the current address by one preserves validity of the remaining bounded
  string, under the generated character-conversion, bounded-string-length,
  address-order, memory-validity, linking, constancy, integer-range,
  offset-alignment, and no-earlier-match assumptions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCSint32, NTP4VCUint64, and NTP4VCValidStrn directly expand the
  corresponding source definitions.

  The arbitrary relations J and K represent addr_le and addr_lt, with their
  source laws under equal bases retained explicitly. The arbitrary map G and
  sets H and I represent region, linked, and sconst. L and M represent
  to_sint8 and to_uint64, while N represents l_strnlen; their source range,
  identity, and fixed-point laws are retained as explicit hypotheses without
  assigning stronger properties to these symbols.

  Every source let-binding is expanded at its uses. All addresses, integers,
  functions, relations, and predicates retain their unrestricted source
  domains. The existential null-position witnesses in the bounded-string
  assumptions and conclusion remain internal, and the no-earlier-match
  assumption retains its full address quantifier and implication scope.
  Splitting the source implication chain into scoped essential hypotheses is
  bidirectionally equivalent to the original statement. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCSint32Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCAddrLt NTP4VCValidRW
  NTP4VCSint8 NTP4VCSint32 NTP4VCUint64 NTP4VCValidStrn
  NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-addr-lt-syntax $a wff ( NTP4VCAddrLt A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-strn-syntax $a wff ( NTP4VCValidStrn A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
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

ntp4vc-addr-lt-def $a |- ( ( NTP4VCAddrLt A B C ) <->
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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
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
     A=t_1, B=a, C=i_1, D=a_1, E=i, and F=t.
     G is region; H and I are the linked and sconst extensions; J and K are
     the addr_le and addr_lt extensions; L and M are to_sint8 and to_uint64;
     and N is l_strnlen. Source lets are expanded as:
       x=A(B), x_1=L(C), x_2=offset(D), x_3=E+offset(D),
       x_4=offset(B), x_6=E+offset(D)-offset(B), and
       x_7=NTP4VCStrnlen(N,A,D,E). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- C e. ZZ $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- I C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- J C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-addr-lt-relation $e |- K C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-sint8-function $e |- L e. ( ZZ ^m ZZ ) $.
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
        ( NTP4VCAddrLe J x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-addr-lt-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLt K x y )
        <->
        ( NTP4VCOffset x ) < ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-sint8-range $e |- A. x e. ZZ
    ( NTP4VCSint8 ( L ` x ) ) $.

  ntp4vc-to-sint8-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint8 x )
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

  ntp4vc-current-value-nonzero $e |- ( A ` B ) =/= 0 $.

  ntp4vc-current-value-not-target $e |- (
    ( A ` B ) =/= ( L ` C )
  ) $.

  ntp4vc-not-at-boundary $e |- (
    ( E + ( NTP4VCOffset D ) ) =/= ( NTP4VCOffset B )
  ) $.

  ntp4vc-remaining-length-alignment $e |- (
    (
      ( NTP4VCOffset B )
      +
      (
        NTP4VCStrnlen
          N A B
          ( ( E + ( NTP4VCOffset D ) ) - ( NTP4VCOffset B ) )
      )
    )
    =
    (
      ( NTP4VCOffset D )
      +
      ( NTP4VCStrnlen N A D E )
    )
  ) $.

  ntp4vc-a1-offset-le-a-offset $e |- (
    ( NTP4VCOffset D ) <_ ( NTP4VCOffset B )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( G ` ( NTP4VCBase D ) ) <_ 0
  ) $.

  ntp4vc-a-offset-within-bound $e |- (
    ( NTP4VCOffset B ) <_ ( E + ( NTP4VCOffset D ) )
  ) $.

  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-sconst-memory $e |- A e. I $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 E ) $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe J D B ) $.
  ntp4vc-current-value-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a1-valid-bounded-string $e |- ( NTP4VCValidStrn F A D E ) $.

  ntp4vc-remaining-count-uint64 $e |- (
    NTP4VCUint64
      ( ( E + ( NTP4VCOffset D ) ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      J
      B
      ( NTP4VCShift D ( NTP4VCStrnlen N A D E ) )
  ) $.

  ntp4vc-a-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      F A B
      ( ( E + ( NTP4VCOffset D ) ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-no-earlier-match $e |- A. x e. NTP4VCAddr
    (
      ( NTP4VCAddrLt K x B )
      ->
      (
        ( NTP4VCAddrLe J D x )
        ->
        ( A ` x ) =/= ( L ` C )
      )
    ) $.

  ntp4vc-strnchr-loop-inv-4-preserved-goal5 $a |- (
    NTP4VCValidStrn
      F
      A
      ( NTP4VCShift B 1 )
      (
        M
        `
        (
          ( ( E + ( NTP4VCOffset D ) ) - 1 )
          -
          ( NTP4VCOffset B )
        )
      )
  ) $.
$}
