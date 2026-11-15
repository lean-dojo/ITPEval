$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strlen_Why3_ide_VCstrlen_loop_inv_3_preserved_goal6:
  the strlen loop-invariant preservation condition concludes that one plus
  the current address offset and the string length at the successor address
  equals the terminating offset computed from the initial address, under the
  generated string-length, memory-validity, address-order, linking,
  constancy, signed-byte-range, offset-alignment, and valid-string
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint8,
  NTP4VCUint64, and NTP4VCValidStr directly expand the corresponding source
  definitions.

  The arbitrary integer-valued map E represents region. Membership of the
  allocation map D in the arbitrary set F represents linked, while membership
  of the integer memory A in the arbitrary set G represents sconst. The
  arbitrary relation H represents addr_le, with its source law under equal
  bases retained explicitly. The arbitrary higher-order map I represents
  l_strlen, and J represents to_uint64; their fixed-point, range, and identity
  laws retain the relevant imported source theory without assigning stronger
  properties to either symbol.

  All four source let-bindings are expanded at their uses. All addresses,
  integers, maps, relations, and predicates keep their original unrestricted
  domains. The existential null-position witness in NTP4VCValidStr remains
  internal. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSint8 NTP4VCUint64
  NTP4VCValidStr NTP4VCStrlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

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
  $d x y A B C D E F G H I J $.

  $( Source parameters:
     A=t_1, B=a, C=a_1, and D=t.
     E is region; F and G are the linked and sconst extensions; H is the
     addr_le extension; I is l_strlen; and J is to_uint64.
     The source lets are expanded as
       x=A(B), x_1=NTP4VCStrlen(I,A,C),
       x_2=offset(C)+x_1, and x_3=offset(B). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- C e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- D e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- F C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- G C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- H C_ ( NTP4VCAddr X. NTP4VCAddr ) $.
  ntp4vc-strlen-function $e |- I e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.
  ntp4vc-to-uint64-function $e |- J e. ( ZZ ^m ZZ ) $.

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
    ( NTP4VCUint64 ( J ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( J ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen I x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( J ` ( 1 + ( NTP4VCStrlen I x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen I x y ) ) $.

  ntp4vc-current-byte-nonzero $e |- ( A ` B ) =/= 0 $.

  ntp4vc-offset-alignment $e |- (
    ( ( NTP4VCOffset C ) + ( NTP4VCStrlen I A C ) )
    =
    ( ( NTP4VCOffset B ) + ( NTP4VCStrlen I A B ) )
  ) $.

  ntp4vc-region-a1 $e |- ( E ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- D e. F $.
  ntp4vc-sconst-memory $e |- A e. G $.
  ntp4vc-a1-le-a $e |- ( NTP4VCAddrLe H C B ) $.
  ntp4vc-current-byte-sint8 $e |- ( NTP4VCSint8 ( A ` B ) ) $.
  ntp4vc-a-valid-string $e |- ( NTP4VCValidStr D A B ) $.
  ntp4vc-a1-valid-string $e |- ( NTP4VCValidStr D A C ) $.

  ntp4vc-a-le-a1-end $e |- (
    NTP4VCAddrLe
      H
      B
      ( NTP4VCShift C ( NTP4VCStrlen I A C ) )
  ) $.

  ntp4vc-strlen-loop-inv-3-preserved-goal6 $a |- (
    (
      ( 1 + ( NTP4VCOffset B ) )
      +
      ( NTP4VCStrlen I A ( NTP4VCShift B 1 ) )
    )
    =
    (
      ( NTP4VCOffset C )
      +
      ( NTP4VCStrlen I A C )
    )
  ) $.
$}
