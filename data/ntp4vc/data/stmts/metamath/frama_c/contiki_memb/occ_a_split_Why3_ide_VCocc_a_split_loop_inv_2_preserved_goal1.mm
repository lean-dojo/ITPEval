$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_memb/occ_a_split_Why3_ide_VCocc_a_split_loop_inv_2_preserved_goal1:
  the occurrence-count split loop invariant is preserved when its upper
  endpoint advances by one, under the generated index-order, memory-region,
  constancy, and signed-32 integer assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented by ZZ X. ZZ, with base and offset given by 1st
  and 2nd, and NTP4VCShift directly expands the source address shift.
  NTP4VCSint32 directly expands the source signed-32 range predicate.

  NTP4VCOccA is the finite cardinality of exactly those integer indices in
  the source half-open interval whose shifted memory value equals the
  requested value. This is the extensional function characterized by the
  source l_occ_a endpoint and iteration axioms.

  The arbitrary integer-valued map R represents the source region function,
  while membership of the arbitrary address-to-integer map A in the arbitrary
  set S represents the source sconst predicate. The source let bindings
  x=l_occ_a(A,B,C,D,E) and x_1=1+F are expanded at every use. The implication
  chain is represented by the displayed essential hypotheses. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCSint32Limit NTP4VCSint32 NTP4VCOccA
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-occ-a-class $a class ( NTP4VCOccA A B C D E ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

${
  $d x A B C D E $.
  ntp4vc-occ-a-def $a |- ( NTP4VCOccA A B C D E ) =
    (
      #
      `
      {
        x e. ZZ
        |
        (
          D <_ x
          /\
          (
            x < E
            /\
            ( A ` ( NTP4VCShift C x ) ) = B
          )
        )
      }
    ) $.
$}

${
  $d A B C D E F H R S $.

  $( Source parameters:
     A=t, B=i_3, C=a, D=i_2, E=i_4, F=i_1, H=i,
     R=region, and S=sconst extension.
     Source lets are expanded as x=NTP4VCOccA(A,B,C,D,E) and x_1=1+F. $)

  ntp4vc-memory-map $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i3-integer $e |- B e. ZZ $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-i4-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-i-integer $e |- H e. ZZ $.
  ntp4vc-region-map $e |- R e. ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- S C_ ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-occurrence-split $e |- (
    (
      ( NTP4VCOccA A B C D E )
      +
      ( NTP4VCOccA A B C E F )
    )
    =
    ( NTP4VCOccA A B C D F )
  ) $.

  ntp4vc-i1-le-i $e |- F <_ H $.
  ntp4vc-i4-le-i $e |- E <_ H $.
  ntp4vc-i1-lt-i $e |- F < H $.
  ntp4vc-i4-le-i1 $e |- E <_ F $.
  ntp4vc-i2-le-i4 $e |- D <_ E $.
  ntp4vc-region-a $e |- ( R ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-i1-max-index $e |- F <_ NTP4VCMaxIndex $.
  ntp4vc-sconst-memory $e |- A e. S $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 B ) $.
  ntp4vc-i4-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-i1-plus-one-sint32 $e |- ( NTP4VCSint32 ( 1 + F ) ) $.

  ntp4vc-occ-a-split-loop-inv-2-preserved-goal1 $a |- (
    (
      ( NTP4VCOccA A B C D E )
      +
      ( NTP4VCOccA A B C E ( 1 + F ) )
    )
    =
    ( NTP4VCOccA A B C D ( 1 + F ) )
  ) $.
$}
