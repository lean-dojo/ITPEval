$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/memchr_Why3_ide_VCmemchr_loop_inv_5_preserved_goal6:
  the memchr loop-invariant preservation condition states that the byte at a
  generated nonnegative offset does not equal the searched signed-byte value,
  under the generated integer bounds, memory validity, address-order,
  linking, constancy, byte-range, and quantified earlier-byte assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCUint32,
  NTP4VCSint32, and NTP4VCSint8 directly expand the corresponding source
  definitions.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map G in the arbitrary set L represents
  linked, while membership of the integer memory D in the arbitrary set S
  represents sconst. The arbitrary relation U represents addr_le, with its
  source law under equal bases retained as an explicit hypothesis. Thus no
  extra laws are assigned to the imported uninterpreted symbols.

  The source occurrences to_sint8 i_3 and to_uint32 (i - 1) are displayed as
  i_3 and i - 1. The explicit signed-byte bounds imply is_sint8 i_3, while
  nonzero uint32 i implies that i - 1 is uint32; the imported source axioms
  id_sint8 and id_uint32 therefore make both replacements bidirectionally
  equivalent in this verification condition. Source let-bindings are
  expanded at every use, and the quantified no-match condition keeps its full
  integer domain. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit NTP4VCSint8Limit
  NTP4VCAddrLe NTP4VCValidRW
  NTP4VCUint32 NTP4VCSint32 NTP4VCSint8
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-addr-le-def $a |- ( ( NTP4VCAddrLe A B C ) <->
  <. B , C >. e. A ) $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

${
  $d x y A B C D E F G L R S U $.

  $( Source parameters:
     A=a, B=i_1, C=i, D=t_1, E=i_3, F=i_2, G=t.
     R is region; L and S are the linked and sconst extensions; U is the
     addr_le extension. Source lets are expanded as
       a_1=shift(A,B-C), x=D(a_1), and x_1=E. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- B e. ZZ $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i3-integer $e |- E e. ZZ $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-addr-le-relation $e |- U C_ ( NTP4VCAddr X. NTP4VCAddr ) $.

  ntp4vc-addr-le-law $e |- A. x e. NTP4VCAddr A. y e. NTP4VCAddr
    (
      ( NTP4VCBase x ) = ( NTP4VCBase y )
      ->
      (
        ( NTP4VCAddrLe U x y )
        <->
        ( NTP4VCOffset x ) <_ ( NTP4VCOffset y )
      )
    ) $.

  ntp4vc-i-nonzero $e |- C =/= 0 $.

  ntp4vc-current-byte-not-target $e |- (
    ( D ` ( NTP4VCShift A ( B - C ) ) ) =/= E
  ) $.

  ntp4vc-i1-positive $e |- 0 < B $.
  ntp4vc-i-nonnegative $e |- 0 <_ C $.
  ntp4vc-i-le-i1 $e |- C <_ B $.
  ntp4vc-i2-nonnegative $e |- 0 <_ F $.

  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-index-bound $e |- ( F + ( C - 1 ) ) < B $.

  ntp4vc-i3-lower-bound $e |- -u ; ; 1 2 8 <_ E $.
  ntp4vc-i3-upper-bound $e |- E <_ ; ; 1 2 7 $.

  ntp4vc-linked-allocation $e |- G e. L $.
  ntp4vc-sconst-memory $e |- D e. S $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-memory-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCShift A 0 ) B
  ) $.

  ntp4vc-start-le-current $e |- (
    NTP4VCAddrLe U A ( NTP4VCShift A ( B - C ) )
  ) $.

  ntp4vc-current-le-end $e |- (
    NTP4VCAddrLe
      U
      ( NTP4VCShift A ( B - C ) )
      ( NTP4VCShift A B )
  ) $.

  ntp4vc-current-byte-sint8 $e |- (
    NTP4VCSint8 ( D ` ( NTP4VCShift A ( B - C ) ) )
  ) $.

  ntp4vc-earlier-bytes-no-target $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        ( x + C ) < B
        ->
        ( D ` ( NTP4VCShift A x ) ) =/= E
      )
    ) $.

  ntp4vc-memchr-loop-inv-5-preserved-goal6 $a |- (
    ( D ` ( NTP4VCShift A F ) ) =/= E
  ) $.
$}
