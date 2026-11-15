$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/search_n/search_n_Why3_ide_VCsearch_n_no_match_post_result_goal16:
  the search_n no-match post-result verification condition concludes that
  the returned index equals the no-match result index, under the generated
  integer-range, allocation, readable-memory, constant-subrange, and nested
  search-branch assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCUint32,
  NTP4VCSint32, NTP4VCConstantRange, and NTP4VCHasConstantSubrange directly
  expand the corresponding source definitions. All quantified indices,
  including the existential constant-subrange witness, retain the full
  integer domain.

  The arbitrary integer map M represents region, and membership of the
  allocation map F in the arbitrary set N represents linked. The arbitrary
  integer function O represents to_uint32; its source range and identity laws
  are retained as universally quantified scoped hypotheses. Source
  let-bindings are expanded at each use.

  Each proposition-valued if is rendered by the bidirectionally equivalent
  guarded disjunction of its then and else branches. Splitting the source
  implication chain into scoped essential hypotheses preserves its universal
  closure over the displayed arbitrary parameters. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
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
  $d x A B C D E F G H I J K L M N O $.

  $( Source parameters:
     A=t_1, B=a, C=i, D=i_7, E=i_3, F=t, G=i_1, H=i_2,
     I=i_4, J=i_5, K=i_6, and L=i_8.
     M is region, N is the extension of linked, and O is to_uint32.
     The source lets are expanded as
       x=A(shift(B,C-1)), x_1=1+D, a_1=shift(B,D),
       and x_2=E+O(1+D). $)

  ntp4vc-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i-integer $e |- C e. ZZ $.
  ntp4vc-i7-integer $e |- D e. ZZ $.
  ntp4vc-i3-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.
  ntp4vc-i1-integer $e |- G e. ZZ $.
  ntp4vc-i2-integer $e |- H e. ZZ $.
  ntp4vc-i4-integer $e |- I e. ZZ $.
  ntp4vc-i5-integer $e |- J e. ZZ $.
  ntp4vc-i6-integer $e |- K e. ZZ $.
  ntp4vc-i8-integer $e |- L e. ZZ $.

  ntp4vc-region-map $e |- M e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- N C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-function $e |- O e. ( ZZ ^m ZZ ) $.

  ntp4vc-to-uint32-range-law $e |- A. x e. ZZ
    ( NTP4VCUint32 ( O ` x ) ) $.

  ntp4vc-to-uint32-identity-law $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( O ` x ) = x
    ) $.

  ntp4vc-region-assumption $e |- (
    ( M ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-assumption $e |- F e. N $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 I ) $.
  ntp4vc-i5-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-i6-uint32 $e |- ( NTP4VCUint32 K ) $.
  ntp4vc-i7-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i8-sint32 $e |- ( NTP4VCSint32 L ) $.

  ntp4vc-no-constant-subrange $e |- (
    -. ( NTP4VCHasConstantSubrange A B J E L )
  ) $.

  ntp4vc-readable-prefix $e |- (
    NTP4VCValidRD F ( NTP4VCShift B 0 ) J
  ) $.

  ntp4vc-prior-value-sint32 $e |- (
    NTP4VCSint32
      ( A ` ( NTP4VCShift B ( C - 1 ) ) )
  ) $.

  ntp4vc-no-match-branch $e |- (
    (
      0 < E
      /\
      (
        (
          E <_ J
          /\
          (
            J = I
            /\
            (
              K = I
              /\
              (
                K = J
                /\
                (
                  C <_ ( 1 + D )
                  /\
                  (
                    NTP4VCConstantRange A B C D L
                    /\
                    (
                      -. ( NTP4VCHasConstantSubrange A B D E L )
                      /\
                      (
                        (
                          (
                            D < J
                            /\
                            (
                              ( C + E ) = ( 1 + D )
                              /\
                              (
                                ( G + E ) = ( 1 + D )
                                /\
                                (
                                  ( H + E ) = ( 1 + D )
                                  /\
                                  (
                                    ( A ` ( NTP4VCShift B D ) ) = L
                                    /\
                                    (
                                      D < ( E + ( O ` ( 1 + D ) ) )
                                      /\
                                      (
                                        D <_ NTP4VCUint32MaxMinusOne
                                        /\
                                        (
                                          ( E + ( O ` ( 1 + D ) ) )
                                          <_
                                          ( NTP4VCUint32Limit + D )
                                          /\
                                          (
                                            NTP4VCValidRD
                                              F
                                              ( NTP4VCShift B D )
                                              1
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                          \/
                          (
                            -. ( D < J )
                            /\
                            J = H
                          )
                        )
                        /\
                        (
                          0 < C
                          ->
                          (
                            A ` ( NTP4VCShift B ( C - 1 ) )
                          )
                          =/=
                          L
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
        \/
        (
          -. ( E <_ J )
          /\
          J = H
        )
      )
    )
    \/
    (
      -. ( 0 < E )
      /\
      H = 0
    )
  ) $.

  ntp4vc-search-n-no-match-post-result-goal16 $a |- J = H $.
$}
