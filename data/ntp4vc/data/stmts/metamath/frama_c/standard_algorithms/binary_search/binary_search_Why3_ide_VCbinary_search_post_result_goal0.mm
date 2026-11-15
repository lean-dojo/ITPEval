$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/binary_search/binary_search_Why3_ide_VCbinary_search_post_result_goal0:
  the binary-search postcondition states that an occurrence of the target in
  the searched prefix exists exactly when the returned result flag is nonzero,
  under the generated bounds, sortedness, lower- and strict-upper-bound,
  integer-range, memory-validity, region, linking, and branch assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCUint32,
  NTP4VCSint32, NTP4VCSorted, NTP4VCLowerBound, and
  NTP4VCStrictUpperBound directly expand the corresponding source
  definitions. Every quantified array index ranges over all of ZZ.

  The arbitrary integer-valued map H represents the source region function,
  and membership of the allocation map E in the arbitrary set I represents
  linked. No additional laws are assigned to either imported symbol. The
  source let-bound address a_1 and value x are expanded at every use.

  Each source proposition-valued if is rendered by the equivalent guarded
  disjunction (condition and then-branch) or (negated condition and
  else-branch). Integer comparisons are decidable, so this preserves both
  branches exactly. Splitting the source implication chain into displayed
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database adds no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32
  NTP4VCSorted NTP4VCLowerBound NTP4VCStrictUpperBound
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
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
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-strict-upper-bound-syntax
  $a wff ( NTP4VCStrictUpperBound A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
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

  ntp4vc-lower-bound-def $a |- (
    ( NTP4VCLowerBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          E <_ ( A ` ( NTP4VCShift B x ) )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.

  ntp4vc-strict-upper-bound-def $a |- (
    ( NTP4VCStrictUpperBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) < E
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  $d x F $.  $d x G $.  $d x H $.  $d x I $.

  $( Source parameters:
     A=a, B=i_2, C=t_1, D=i_1, E=t, F=i, and G=i_3.
     H is region and I is the extension of linked. Source lets are expanded
     as a_1=NTP4VCShift(A,B) and x=C(a_1). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- B e. ZZ $.
  ntp4vc-value-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-allocation-map $e |- E e. ( ZZ ^m ZZ ) $.
  ntp4vc-target-integer $e |- F e. ZZ $.
  ntp4vc-result-integer $e |- G e. ZZ $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i2-le-i1 $e |- B <_ D $.
  ntp4vc-i2-nonnegative $e |- 0 <_ B $.
  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- E e. I $.

  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-target-sint32 $e |- ( NTP4VCSint32 F ) $.
  ntp4vc-result-sint32 $e |- ( NTP4VCSint32 G ) $.

  ntp4vc-array-sorted $e |- (
    NTP4VCSorted C A 0 D
  ) $.

  ntp4vc-current-value-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCShift A B ) )
  ) $.

  ntp4vc-suffix-lower-bound $e |- (
    NTP4VCLowerBound C A B D F
  ) $.

  ntp4vc-prefix-strict-upper-bound $e |- (
    NTP4VCStrictUpperBound C A 0 B F
  ) $.

  ntp4vc-array-valid-rd $e |- (
    NTP4VCValidRD E ( NTP4VCShift A 0 ) D
  ) $.

  ntp4vc-result-branch $e |- (
    (
      B < D
      /\
      (
        ( NTP4VCValidRD E ( NTP4VCShift A B ) 1 )
        /\
        (
          (
            ( C ` ( NTP4VCShift A B ) ) <_ F
            /\
            G = 1
          )
          \/
          (
            -. ( ( C ` ( NTP4VCShift A B ) ) <_ F )
            /\
            G = 0
          )
        )
      )
    )
    \/
    (
      -. ( B < D )
      /\
      G = 0
    )
  ) $.

  ntp4vc-binary-search-post-result-goal0 $a |- (
    (
      E. x e. ZZ
        (
          ( C ` ( NTP4VCShift A x ) ) = F
          /\
          (
            0 <_ x
            /\
            x < D
          )
        )
    )
    <->
    G =/= 0
  ) $.
$}
