$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_loop_inv_not_found_preserved_goal4:
  the search_n loop-invariant preservation condition states that extending
  the searched prefix by one preserves the absence of a constant subrange
  of the requested positive length, under the generated integer-range,
  linking, readable-memory, prior-range, and branch assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCUint32,
  NTP4VCSint32, NTP4VCConstantRange, and NTP4VCHasConstantSubrange directly
  expand the corresponding source definitions. Every integer quantifier,
  including the existential constant-subrange witness, retains the full
  integer domain, and the memory and allocation maps remain arbitrary total
  functions.

  The arbitrary integer map J represents region, and membership of the
  allocation map G in the arbitrary set K represents linked. Source
  let-bindings are expanded at each use. Splitting the source implication
  chain into scoped essential hypotheses is bidirectionally equivalent for
  the arbitrary displayed parameters. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCUint32MaxMinusOne
  NTP4VCValidRD NTP4VCUint32 NTP4VCSint32
  NTP4VCConstantRange NTP4VCHasConstantSubrange
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-max-minus-one-class
  $a class NTP4VCUint32MaxMinusOne $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-constant-range-syntax
  $a wff ( NTP4VCConstantRange A B C D E ) $.
ntp4vc-has-constant-subrange-syntax
  $a wff ( NTP4VCHasConstantSubrange A B C D E ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-max-minus-one-def
  $a |- NTP4VCUint32MaxMinusOne =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.

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
  $d x A B C D E $.
  ntp4vc-constant-range-def $a |- (
    ( NTP4VCConstantRange A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) = E
        )
      )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-has-constant-subrange-def $a |- (
    ( NTP4VCHasConstantSubrange A B C D E )
    <->
    E. x e. ZZ
      (
        0 <_ x
        /\
        (
          ( D + x ) <_ C
          /\
          ( NTP4VCConstantRange A B x ( D + x ) E )
        )
      )
  ) $.
$}

${
  $d x A B C D E F G H I J K $.

  $( Source parameters:
     A=i_4, B=a, C=t_1, D=i, E=i_2, F=i_3, G=t, H=i_1,
     and I=i_5. J is region, and K is the extension of linked.
     The source lets are expanded as x=1+A, a_1=shift(B,A),
     x_1=C(shift(B,A)), and x_2=C(shift(B,D-1)). $)

  ntp4vc-i4-integer $e |- A e. ZZ $.
  ntp4vc-address $e |- B e. NTP4VCAddr $.
  ntp4vc-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i3-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-i1-integer $e |- H e. ZZ $.
  ntp4vc-i5-integer $e |- I e. ZZ $.

  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.

  ntp4vc-length-positive $e |- 0 < E $.
  ntp4vc-length-within-bound $e |- E <_ F $.
  ntp4vc-current-index-within-bound $e |- A < F $.
  ntp4vc-region-assumption $e |- (
    ( J ` ( NTP4VCBase B ) ) <_ 0
  ) $.
  ntp4vc-current-index-max $e |- A <_ NTP4VCUint32MaxMinusOne $.
  ntp4vc-start-before-next-index $e |- D <_ ( 1 + A ) $.
  ntp4vc-linked-assumption $e |- G e. K $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-i5-sint32 $e |- ( NTP4VCSint32 I ) $.
  ntp4vc-next-index-uint32 $e |- (
    NTP4VCUint32 ( 1 + A )
  ) $.
  ntp4vc-current-value-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCShift B A ) )
  ) $.

  ntp4vc-prior-constant-range $e |- (
    NTP4VCConstantRange C B D A I
  ) $.
  ntp4vc-prior-no-constant-subrange $e |- (
    -. ( NTP4VCHasConstantSubrange C B A E I )
  ) $.

  ntp4vc-readable-prefix $e |- (
    NTP4VCValidRD G ( NTP4VCShift B 0 ) F
  ) $.
  ntp4vc-readable-current-value $e |- (
    NTP4VCValidRD G ( NTP4VCShift B A ) 1
  ) $.
  ntp4vc-prior-value-sint32 $e |- (
    NTP4VCSint32
      ( C ` ( NTP4VCShift B ( D - 1 ) ) )
  ) $.
  ntp4vc-prior-value-different $e |- (
    0 < D
    ->
    ( C ` ( NTP4VCShift B ( D - 1 ) ) ) =/= I
  ) $.

  ntp4vc-loop-branch $e |- (
    ( C ` ( NTP4VCShift B A ) ) =/= I
    \/
    (
      H = D
      /\
      (
        ( H + E ) =/= ( 1 + A )
        /\
        (
          H <_ ( 1 + A )
          /\
          A <_ ( NTP4VCUint32MaxMinusOne + H )
        )
      )
    )
  ) $.

  ntp4vc-search-n-loop-inv-not-found-preserved-goal4 $a |- (
    -. ( NTP4VCHasConstantSubrange C B ( 1 + A ) E I )
  ) $.
$}
