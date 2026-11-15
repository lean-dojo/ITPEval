$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3:
  advancing the lower index of a list search preserves its upper-bound
  sentinel result under the generated range, framing, region, signed-32-bit,
  and no-matching-item loop-invariant conditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCSint32, and NTP4VCFramed directly expand
  the corresponding source definitions.

  NTP4VCIndexOfEq is the graph of the source l_index_of operation: when the
  upper bound is at most the lower bound its result is the upper-bound
  sentinel; otherwise it is the least matching integer position in the
  half-open interval, or the upper-bound sentinel if there is no match. For
  the nonnegative lower bounds in this statement, this is bidirectionally
  equivalent to the source Q_no_more_elements, Q_found_item, and
  Q_not_the_item axioms.

  The let-bound x is expanded as 1 + i_1. Both source universal loop
  assumptions retain their integer domains and implication nesting; in
  particular, the search equality in the second one remains inside the
  quantifier even though it is independent of the quantified index. The
  source region function is an arbitrary integer map. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint32 NTP4VCFramed NTP4VCIndexOfEq
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-framed-syntax
  $a wff ( NTP4VCFramed A B ) $.
ntp4vc-index-of-eq-syntax
  $a wff ( NTP4VCIndexOfEq A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u ( 2 ^ ; 3 1 ) <_ A /\ A < ( 2 ^ ; 3 1 ) )
) $.

${
  $d x A $.
  $d x B $.
  ntp4vc-framed-def $a |- ( ( NTP4VCFramed A B ) <->
    A. x e. NTP4VCAddr
      ( ( A ` ( NTP4VCBase ( B ` x ) ) ) <_ 0 )
  ) $.
$}

${
  $d x A $.
  $d x B $.
  $d x C $.
  $d x D $.
  $d x E $.
  $d x F $.
  ntp4vc-index-of-eq-def $a |- (
    ( NTP4VCIndexOfEq A B C D E F )
    <->
    (
      ( E <_ D /\ F = E )
      \/
      (
        D < E
        /\
        (
          (
            F = E
            /\
            A. x e. ZZ
            (
              ( D <_ x /\ x < E )
              ->
              ( A ` ( NTP4VCShift C x ) ) =/= B
            )
          )
          \/
          (
            D <_ F
            /\
            (
              F < E
              /\
              (
                ( A ` ( NTP4VCShift C F ) ) = B
                /\
                A. x e. ZZ
                (
                  ( D <_ x /\ x < F )
                  ->
                  ( A ` ( NTP4VCShift C x ) ) =/= B
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
  $d x A $.
  $d x B $.
  $d x C $.
  $d x D $.
  $d x E $.
  $d x F $.
  $d x G $.
  $d x N $.

  $( Source parameters:
     A=t, B=a, C=a_1, D=i_1, E=i, F=i_2, G=i_3, N=region.
     The let-bound x is expanded as 1 + D. $)

  ntp4vc-pointer-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-item-address $e |- B e. NTP4VCAddr $.
  ntp4vc-array-address $e |- C e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i2-integer $e |- F e. ZZ $.
  ntp4vc-i3-integer $e |- G e. ZZ $.
  ntp4vc-region-map $e |- N e. ( ZZ ^m ZZ ) $.

  ntp4vc-initial-index-of-result $e |- (
    NTP4VCIndexOfEq A B C G E E
  ) $.

  ntp4vc-i1-le-i $e |- D <_ E $.
  ntp4vc-i3-le-i $e |- G <_ E $.
  ntp4vc-i1-lt-i $e |- D < E $.
  ntp4vc-i2-le-i1 $e |- F <_ D $.
  ntp4vc-i3-le-i1 $e |- G <_ D $.
  ntp4vc-i3-le-i2 $e |- G <_ F $.
  ntp4vc-i3-nonnegative $e |- 0 <_ G $.

  ntp4vc-region-item $e |- (
    ( N ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-array $e |- (
    ( N ` ( NTP4VCBase C ) ) <_ 0
  ) $.

  ntp4vc-framed-pointer-map $e |- ( NTP4VCFramed N A ) $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 E ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-i3-sint32 $e |- ( NTP4VCSint32 G ) $.
  ntp4vc-next-i1-sint32 $e |- ( NTP4VCSint32 ( 1 + D ) ) $.

  ntp4vc-no-item-before-i1 $e |- A. x e. ZZ
    (
      x < D
      ->
      (
        G <_ x
        ->
        ( A ` ( NTP4VCShift C x ) ) =/= B
      )
    ) $.

  ntp4vc-index-of-i1-loop-assumption $e |- A. x e. ZZ
    (
      x < D
      ->
      (
        G <_ x
        ->
        ( NTP4VCIndexOfEq A B C D E E )
      )
    ) $.

  ntp4vc-index-of-up-unexisting-item-loop-inv-preserved-goal3 $a |- (
    NTP4VCIndexOfEq A B C ( 1 + D ) E E
  ) $.
$}
