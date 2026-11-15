$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strnlen_Why3_ide_VCstrnlen_null_byte_post_goal11:
  the strnlen null-byte postcondition concludes that the byte at the
  unsigned-64 conversion of the offset from the initial address to the
  current address is zero, under the generated null-byte, length-alignment,
  index-bound, address-order, memory-linking, constancy, integer-range,
  bounded-string, endpoint, signed-byte, branch, and no-earlier-null
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint64, and NTP4VCValidStrn directly expand the corresponding source
  definitions.

  The arbitrary map E and sets F and G represent region, linked, and sconst.
  The arbitrary relation H represents addr_le, with its source law under
  equal bases retained explicitly. I represents to_uint64, while J represents
  l_strnlen; their source range, identity, and fixed-point laws are retained
  as explicit hypotheses without assigning stronger properties to either
  symbol.

  Every source let-binding is expanded at its uses. All addresses, integers,
  functions, relations, and predicates retain their unrestricted source
  domains. In particular, L is the independently quantified source index i,
  not an externalized witness. The null-position witnesses in both
  bounded-string assumptions remain internally existential, and the
  no-earlier-null assumption retains its full integer quantifier and
  implication scope. Splitting the source implication chain into scoped
  essential hypotheses is bidirectionally equivalent to the original
  statement. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStrn
  NTP4VCStrnlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strnlen-class $a class ( NTP4VCStrnlen A B C D ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
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
  $d x y z A B C D E F G H I J K L $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, K=i_1, L=i, and D=t.
     E is region; F and G are the linked and sconst extensions; H is the
     addr_le extension; I is to_uint64; and J is l_strnlen. Source lets are
     expanded as:
       x=offset(B), x_1=offset(C),
       x_2=K+offset(C)-offset(B),
       x_3=NTP4VCStrnlen(J,A,C,K),
       x_4=K+offset(C), and
       x_5=A(NTP4VCShift(C,I(offset(B)-offset(C)))). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- K e. ZZ $.
  ntp4vc-i-integer $e |- L e. ZZ $.
  ntp4vc-allocation-map $e |- D e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- F C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- G C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- H C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-to-uint64-function $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-strnlen-function $e |- J e.
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
        ( NTP4VCAddrLe H x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( I ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( I ` x ) = x
    ) $.

  ntp4vc-strnlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          (
            ( NTP4VCStrnlen J x y z )
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
                I
                `
                (
                  1
                  +
                  (
                    NTP4VCStrnlen
                      J
                      x
                      ( NTP4VCShift y 1 )
                      ( I ` ( z - 1 ) )
                  )
                )
              )
            )
          ) $.

  ntp4vc-strnlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          ( NTP4VCUint64 ( NTP4VCStrnlen J x y z ) ) $.

  ntp4vc-null-byte-at-i $e |- (
    ( A ` ( NTP4VCShift C L ) ) = 0
  ) $.

  ntp4vc-length-alignment $e |- (
    (
      ( NTP4VCOffset B )
      +
      (
        NTP4VCStrnlen
          J A B
          ( ( K + ( NTP4VCOffset C ) ) - ( NTP4VCOffset B ) )
      )
    )
    =
    (
      ( NTP4VCOffset C )
      +
      ( NTP4VCStrnlen J A C K )
    )
  ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ L $.
  ntp4vc-i-le-i1 $e |- L <_ K $.

  ntp4vc-a1-offset-le-a-offset $e |- (
    ( NTP4VCOffset C ) <_ ( NTP4VCOffset B )
  ) $.

  ntp4vc-region-a1 $e |- (
    ( E ` ( NTP4VCBase C ) ) <_ 0
  ) $.

  ntp4vc-a-offset-le-count-endpoint $e |- (
    ( NTP4VCOffset B ) <_ ( K + ( NTP4VCOffset C ) )
  ) $.

  ntp4vc-linked-allocation $e |- D e. F $.
  ntp4vc-sconst-memory $e |- A e. G $.
  ntp4vc-i1-uint64 $e |- ( NTP4VCUint64 K ) $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe H C B ) $.

  ntp4vc-a1-valid-bounded-string $e |- (
    NTP4VCValidStrn D A C K
  ) $.

  ntp4vc-remaining-count-uint64 $e |- (
    NTP4VCUint64
      ( ( K + ( NTP4VCOffset C ) ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      H
      B
      ( NTP4VCShift C ( NTP4VCStrnlen J A C K ) )
  ) $.

  ntp4vc-a-valid-remaining-bounded-string $e |- (
    NTP4VCValidStrn
      D A B
      ( ( K + ( NTP4VCOffset C ) ) - ( NTP4VCOffset B ) )
  ) $.

  ntp4vc-offset-byte-sint8 $e |- (
    NTP4VCSint8
      (
        A
        `
        (
          NTP4VCShift
            C
            ( I ` ( ( NTP4VCOffset B ) - ( NTP4VCOffset C ) ) )
        )
      )
  ) $.

  ntp4vc-null-or-at-count-endpoint $e |- (
    ( A ` B ) = 0
    \/
    ( K + ( NTP4VCOffset C ) ) = ( NTP4VCOffset B )
  ) $.

  ntp4vc-no-null-before-a-offset $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + ( NTP4VCOffset C ) ) < ( NTP4VCOffset B )
        ->
        ( A ` ( NTP4VCShift C x ) ) =/= 0
      )
    ) $.

  ntp4vc-strnlen-null-byte-post-goal11 $a |- (
    (
      A
      `
      (
        NTP4VCShift
          C
          ( I ` ( ( NTP4VCOffset B ) - ( NTP4VCOffset C ) ) )
      )
    )
    =
    0
  ) $.
$}
