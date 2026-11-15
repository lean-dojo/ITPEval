$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/contiki_list/index_of_Why3_ide_VCindex_of_post_part2_goal1:
  the list index search returns the first array position whose pointer equals
  the selected item, under the generated integer bounds, memory validity,
  framing, linkage, and signed-32-bit conditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given by
  1st and 2nd. NTP4VCShift, NTP4VCValidRW, NTP4VCSint32, and NTP4VCFramed
  directly expand the corresponding source definitions.

  NTP4VCIndexOfEq is the graph of the source l_index_of operation: when the
  upper bound is at most the lower bound its result is the upper-bound
  sentinel; otherwise it is the least matching integer position in the
  half-open interval, or the upper-bound sentinel if there is no match. For a
  nonnegative lower bound this is bidirectionally equivalent to the source
  Q_no_more_elements, Q_found_item, and Q_not_the_item axioms.

  The let-bound item address is expanded at every use. The source region
  function and linked predicate have no constraining axioms used here, so they
  are represented by an arbitrary integer map and an arbitrary subset of
  integer maps. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCValidRW NTP4VCSint32 NTP4VCFramed NTP4VCIndexOfEq
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
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
  $d x N $.
  $d x O $.

  $( Source parameters:
     A=t_1, B=a, C=i_1, D=i, E=i_2, F=t,
     N=region, O=linked predicate. $)

  ntp4vc-t1-map $e |- A e. ( NTP4VCAddr ^m NTP4VCAddr ) $.
  ntp4vc-array-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- C e. ZZ $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- O C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i-nonnegative $e |- 0 <_ D $.
  ntp4vc-i1-upper-bound $e |- C <_ D $.
  ntp4vc-i1-strict-upper-bound $e |- C < D $.
  ntp4vc-i2-lower-bound $e |- E <_ C $.
  ntp4vc-i2-nonnegative $e |- 0 <_ E $.
  ntp4vc-i2-strict-upper-bound $e |- E < D $.

  ntp4vc-region-array $e |- (
    ( N ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-region-item $e |- (
    (
      N
      `
      (
        NTP4VCBase
        ( A ` ( NTP4VCShift B C ) )
      )
    )
    <_
    0
  ) $.

  ntp4vc-framed-t1 $e |- ( NTP4VCFramed N A ) $.
  ntp4vc-linked-allocation $e |- F e. O $.

  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 C ) $.
  ntp4vc-i2-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-array-valid $e |- (
    E <_ D
    ->
    (
      NTP4VCValidRW
        F
        ( NTP4VCShift B E )
        ( D - E )
    )
  ) $.

  ntp4vc-no-earlier-item $e |- A. x e. ZZ
    (
      x < C
      ->
      (
        E <_ x
        ->
        (
          ( A ` ( NTP4VCShift B C ) )
          =/=
          ( A ` ( NTP4VCShift B x ) )
        )
      )
    ) $.

  ntp4vc-index-of-post-part2-goal1 $a |- (
    NTP4VCIndexOfEq
      A
      ( A ` ( NTP4VCShift B C ) )
      B E D C
  ) $.
$}
