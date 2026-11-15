$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_4_goal11:
  the inner-product verification condition establishes the signed 32-bit
  upper bound for the next accumulated sum, under the generated integer-range,
  product-bound, accumulator-bound, memory-validity, region, and linking
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCSint32,
  NTP4VCUint32, NTP4VCProductBounds, and NTP4VCInnerProductBounds directly
  expand the corresponding source definitions. Every quantified index ranges
  over all of ZZ.

  The arbitrary integer-valued map H represents region, and membership of the
  allocation map G in the arbitrary set I represents linked. J is the source
  to_sint32 function, and K is the curried source l_innerproduct function.
  Their relevant imported source laws are retained as universally quantified
  context hypotheses: to_sint32 has signed-32 range and is the identity on
  signed-32 inputs, while l_innerproduct satisfies Q_InnerProductNext.

  The three source let-bound values are expanded at every use. Splitting the
  source implication chain into displayed hypotheses is bidirectionally
  equivalent for the arbitrary displayed parameters. The final declaration
  is Metamath's native unproved $a statement encoding; this database adds no
  $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCSint32 NTP4VCUint32
  NTP4VCInnerProduct NTP4VCProductBounds NTP4VCInnerProductBounds
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-inner-product-class
  $a class ( NTP4VCInnerProduct A B C D E F ) $.

ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-product-bounds-syntax
  $a wff ( NTP4VCProductBounds A B C D ) $.
ntp4vc-inner-product-bounds-syntax
  $a wff ( NTP4VCInnerProductBounds A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-sint32-def $a |- NTP4VCMaxSint32 =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 7 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

ntp4vc-inner-product-def $a |- (
  ( NTP4VCInnerProduct A B C D E F )
  =
  ( ( ( ( ( A ` B ) ` C ) ` D ) ` E ) ` F )
) $.

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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.

  ntp4vc-product-bounds-def $a |- (
    ( NTP4VCProductBounds A B C D )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < D
          ->
          (
            -u NTP4VCSint32Limit
            <_
            (
              ( A ` ( NTP4VCShift B x ) )
              x.
              ( A ` ( NTP4VCShift C x ) )
            )
            /\
            (
              (
                ( A ` ( NTP4VCShift B x ) )
                x.
                ( A ` ( NTP4VCShift C x ) )
              )
              <_
              NTP4VCMaxSint32
            )
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.
  $d x D $.  $d x E $.  $d x F $.

  ntp4vc-inner-product-bounds-def $a |- (
    ( NTP4VCInnerProductBounds A B C D E F )
    <->
    A. x e. ZZ
      (
        x <_ E
        ->
        (
          0 <_ x
          ->
          (
            -u NTP4VCSint32Limit
            <_
            ( NTP4VCInnerProduct A B C D x F )
            /\
            (
              ( NTP4VCInnerProduct A B C D x F )
              <_
              NTP4VCMaxSint32
            )
          )
        )
      )
  ) $.
$}

${
  $d m p q n k $.
  $d m A $.  $d m B $.  $d m C $.  $d m D $.  $d m E $.
  $d m F $.  $d m G $.  $d m H $.  $d m I $.  $d m J $.
  $d m K $.
  $d p A $.  $d p B $.  $d p C $.  $d p D $.  $d p E $.
  $d p F $.  $d p G $.  $d p H $.  $d p I $.  $d p J $.
  $d p K $.
  $d q A $.  $d q B $.  $d q C $.  $d q D $.  $d q E $.
  $d q F $.  $d q G $.  $d q H $.  $d q I $.  $d q J $.
  $d q K $.
  $d n A $.  $d n B $.  $d n C $.  $d n D $.  $d n E $.
  $d n F $.  $d n G $.  $d n H $.  $d n I $.  $d n J $.
  $d n K $.
  $d k A $.  $d k B $.  $d k C $.  $d k D $.  $d k E $.
  $d k F $.  $d k G $.  $d k H $.  $d k I $.  $d k J $.
  $d k K $.

  $( Source parameters:
     A=t_1, B=a, C=i_2, D=a_1, E=i_1, F=i, and G=t.
     H is region, I is the extension of linked, J is to_sint32, and K is
     l_innerproduct. Source lets are expanded as
       x=A(NTP4VCShift(B,C)),
       x_1=A(NTP4VCShift(D,C)), and
       x_2=NTP4VCInnerProduct(K,A,D,B,C,E). $)

  ntp4vc-value-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i2-integer $e |- C e. ZZ $.
  ntp4vc-a1-address $e |- D e. NTP4VCAddr $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint32-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-inner-product-map $e |- K e.
    (
      (
        (
          (
            ( ( ZZ ^m ZZ ) ^m ZZ )
            ^m
            NTP4VCAddr
          )
          ^m
          NTP4VCAddr
        )
        ^m
        ( ZZ ^m NTP4VCAddr )
      )
    ) $.

  ntp4vc-to-sint32-range $e |- A. m e. ZZ
    ( NTP4VCSint32 ( J ` m ) ) $.

  ntp4vc-to-sint32-identity $e |- A. m e. ZZ
    (
      ( NTP4VCSint32 m )
      ->
      ( J ` m ) = m
    ) $.

  ntp4vc-inner-product-next $e |- A. m e. ( ZZ ^m NTP4VCAddr )
    A. p e. NTP4VCAddr
      A. q e. NTP4VCAddr
        A. n e. ZZ
          A. k e. ZZ
            (
              0 < n
              ->
              (
                ( NTP4VCSint32 k )
                ->
                (
                  (
                    ( NTP4VCInnerProduct K m p q ( n - 1 ) k )
                    +
                    (
                      ( m ` ( NTP4VCShift p ( n - 1 ) ) )
                      x.
                      ( m ` ( NTP4VCShift q ( n - 1 ) ) )
                    )
                  )
                  =
                  ( NTP4VCInnerProduct K m p q n k )
                )
              )
            ) $.

  ntp4vc-i2-le-i $e |- C <_ F $.
  ntp4vc-i2-nonnegative $e |- 0 <_ C $.
  ntp4vc-i2-lt-i $e |- C < F $.

  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( H ` ( NTP4VCBase D ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- G e. I $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 E ) $.

  ntp4vc-product-bounds $e |- (
    NTP4VCProductBounds A D B F
  ) $.

  ntp4vc-x-sint32 $e |- (
    NTP4VCSint32 ( A ` ( NTP4VCShift B C ) )
  ) $.

  ntp4vc-x1-sint32 $e |- (
    NTP4VCSint32 ( A ` ( NTP4VCShift D C ) )
  ) $.

  ntp4vc-inner-product-bounds $e |- (
    NTP4VCInnerProductBounds K A D B F E
  ) $.

  ntp4vc-a-valid-rd $e |- (
    NTP4VCValidRD G ( NTP4VCShift B 0 ) F
  ) $.

  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD G ( NTP4VCShift D 0 ) F
  ) $.

  ntp4vc-x2-sint32 $e |- (
    NTP4VCSint32
      ( NTP4VCInnerProduct K A D B C E )
  ) $.

  ntp4vc-inner-product-assert-rte-signed-overflow-4-goal11 $a |- (
    (
      ( NTP4VCInnerProduct K A D B C E )
      +
      (
        J
        `
        (
          ( A ` ( NTP4VCShift B C ) )
          x.
          ( A ` ( NTP4VCShift D C ) )
        )
      )
    )
    <_
    NTP4VCMaxSint32
  ) $.
$}
