$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_loop_inv_2_established_part2_goal4:
  the memccpy verification condition states that a positive copy length,
  valid separated buffers, integer range conditions, and the generated
  memory-model assumptions place the source endpoint after its start in the
  address order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSeparated,
  NTP4VCUint32, and NTP4VCSint32 directly expand the corresponding source
  definitions.

  The arbitrary integer-valued map R represents the source region function.
  Membership of the allocation map T in the arbitrary set L represents
  linked, while membership of the integer memory E in the arbitrary set S
  represents sconst. The arbitrary relation U represents addr_le, with its
  source law under equal bases retained as an explicit hypothesis. Thus no
  extra laws are assigned to the imported uninterpreted symbols.

  The source let-bindings a_2 = shift(a, 0) and a_3 = shift(a_1, 0) are
  expanded at their uses. The final declaration is Metamath's native unproved
  $a statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCAddrLe NTP4VCValidRW NTP4VCSeparated
  NTP4VCUint32 NTP4VCSint32
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-addr-le-syntax $a wff ( NTP4VCAddrLe A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

${
  $d x y A B C D E L R S T U $.

  $( Source parameters:
     A=a, B=a_1, C=i, D=i_1, T=t, and E=t_1.
     R is region; L and S are the linked and sconst extensions; U is the
     addr_le extension. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-integer-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.

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

  ntp4vc-i-positive $e |- 0 < C $.
  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( R ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-i1-lower-bound $e |- -u ; ; 1 2 8 <_ D $.
  ntp4vc-i1-upper-bound $e |- D <_ ; ; 1 2 7 $.
  ntp4vc-linked-allocation $e |- T e. L $.
  ntp4vc-sconst-memory $e |- E e. S $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 D ) $.

  ntp4vc-destination-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift A 0 ) C
  ) $.

  ntp4vc-source-valid-rw $e |- (
    NTP4VCValidRW T ( NTP4VCShift B 0 ) C
  ) $.

  ntp4vc-buffers-separated $e |- (
    NTP4VCSeparated
      ( NTP4VCShift A 0 ) C
      ( NTP4VCShift B 0 ) C
  ) $.

  ntp4vc-memccpy-loop-inv-2-established-part2-goal4 $a |- (
    NTP4VCAddrLe U B ( NTP4VCShift B C )
  ) $.
$}
