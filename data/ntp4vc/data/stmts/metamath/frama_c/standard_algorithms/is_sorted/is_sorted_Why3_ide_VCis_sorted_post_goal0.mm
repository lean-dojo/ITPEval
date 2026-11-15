$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/is_sorted/is_sorted_Why3_ide_VCis_sorted_post_goal0:
  the is-sorted postcondition states that the array prefix is sorted exactly
  when the returned signed integer flag is nonzero, under the generated
  integer-range, weak-sortedness, branch, memory-validity, region, and
  linkedness assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCUint32,
  NTP4VCSint32, NTP4VCWeaklySorted, and NTP4VCSorted directly expand the
  corresponding source definitions. Every quantified index retains the full
  source domain ZZ, and every memory is an arbitrary total function.

  The source Boolean p is represented by the exactly two-element carrier
  { 0 , 1 }, with false represented by 0. The arbitrary integer-valued map H
  represents region, membership of the allocation map C in the arbitrary set
  I represents linked, and J represents to_uint32. The source range and
  identity laws for to_uint32 are retained as scoped universal hypotheses.

  Source x is expanded to 1+A and source a_1 to NTP4VCShift(B,A). Each
  proposition-valued if is rendered by the equivalent guarded disjunction
  (condition and then-branch) or (negated condition and else-branch).
  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxIndex NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32
  NTP4VCWeaklySorted NTP4VCSorted
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-weakly-sorted-syntax
  $a wff ( NTP4VCWeaklySorted A B C D ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-valid-rd-def $a |- ( ( NTP4VCValidRD A B C ) <->
  (
    0 < C
    ->
    (
      ( NTP4VCBase B ) =/= 0
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

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.

  ntp4vc-weakly-sorted-def $a |- (
    ( NTP4VCWeaklySorted A B C D )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          ( 2 + x ) <_ D
          ->
          (
            ( A ` ( NTP4VCShift B x ) )
            <_
            ( A ` ( NTP4VCShift B ( 1 + x ) ) )
          )
        )
      )
  ) $.
$}

${
  $d x y $.
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
  $d y A $.  $d y B $.  $d y C $.  $d y D $.

  ntp4vc-sorted-def $a |- (
    ( NTP4VCSorted A B C D )
    <->
    A. x e. ZZ A. y e. ZZ
      (
        y < D
        ->
        (
          C <_ x
          ->
          (
            x < y
            ->
            (
              ( A ` ( NTP4VCShift B x ) )
              <_
              ( A ` ( NTP4VCShift B y ) )
            )
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.  $d x J $.

  $( Source parameters:
     A=i_2, B=a, C=t, D=i, E=i_1, F=p, and G=t_1.
     H is region, I is the extension of linked, and J is to_uint32.
     Source lets are expanded as x=1+A and a_1=NTP4VCShift(B,A). $)

  ntp4vc-i2-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- C e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-p-boolean $e |- F e. { 0 , 1 } $.
  ntp4vc-value-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- J e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( J ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( J ` x ) = x
    ) $.

  ntp4vc-region-a $e |- (
    ( H ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- C e. I $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD C ( NTP4VCShift B 0 ) D
  ) $.

  ntp4vc-result-branch $e |- (
    (
      0 < D
      /\
      (
        F = 0
        /\
        (
          ( NTP4VCWeaklySorted G B 0 ( 1 + A ) )
          /\
          (
            (
              ( 2 + A ) <_ D
              /\
              (
                E = 0
                /\
                (
                  ( G ` ( NTP4VCShift B ( 1 + A ) ) )
                  <
                  ( G ` ( NTP4VCShift B A ) )
                  /\
                  (
                    A <_ NTP4VCMaxIndex
                    /\
                    (
                      ( NTP4VCValidRD
                        C
                        ( NTP4VCShift B A )
                        1
                      )
                      /\
                      ( NTP4VCValidRD
                        C
                        ( NTP4VCShift B ( J ` ( 1 + A ) ) )
                        1
                      )
                    )
                  )
                )
              )
            )
            \/
            (
              -. ( ( 2 + A ) <_ D )
              /\
              E = 1
            )
          )
        )
      )
    )
    \/
    (
      -. ( 0 < D )
      /\
      E = 1
    )
  ) $.

  ntp4vc-is-sorted-post-goal0 $a |- (
    ( NTP4VCSorted G B 0 D )
    <->
    E =/= 0
  ) $.
$}
