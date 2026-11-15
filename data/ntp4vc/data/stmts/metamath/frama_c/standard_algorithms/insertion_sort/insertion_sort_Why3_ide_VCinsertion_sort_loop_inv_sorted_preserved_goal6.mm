$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_sorted_preserved_goal6:
  the insertion-sort loop-invariant preservation condition states that the
  updated prefix through one plus the current outer index is sorted, under
  the generated bounds, memory-validity, sortedness, unchanged-range,
  multiset, order-bound, and equal-range assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRD,
  NTP4VCValidRW, NTP4VCSint32, NTP4VCUint32, NTP4VCSorted,
  NTP4VCUnchanged, NTP4VCMultisetUnchanged, NTP4VCUpperBound,
  NTP4VCStrictLowerBound, and NTP4VCEqualRanges directly expand the
  corresponding source definitions. Every integer quantifier retains the
  full source domain ZZ, and every memory is an arbitrary total function
  from addresses to integers.

  The arbitrary maps I and K represent the source region and to_uint32
  operations; membership of H in the arbitrary set J represents linked.
  The curried map L represents l_count_1'. The source range and identity
  laws for to_uint32 and all four source counting laws are retained as
  universally quantified scoped hypotheses. Every source let binding x_1,
  x_2, a_1, a_2, a_3, x_3, a_4, a_5, and a_6 is retained by an explicit
  definition.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCMaxIndex NTP4VCMaxUint32 NTP4VCSint32Limit
  NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCSorted NTP4VCUnchanged NTP4VCMultisetUnchanged
  NTP4VCUpperBound NTP4VCStrictLowerBound NTP4VCEqualRanges
  NTP4VCCount
  NTP4VCX1 NTP4VCX2 NTP4VCX3
  NTP4VCA1 NTP4VCA2 NTP4VCA3 NTP4VCA4 NTP4VCA5 NTP4VCA6
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-max-uint32-class $a class NTP4VCMaxUint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-x1-class $a class ( NTP4VCX1 A B ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D E ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F G ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.
ntp4vc-upper-bound-syntax
  $a wff ( NTP4VCUpperBound A B C D E ) $.
ntp4vc-strict-lower-bound-syntax
  $a wff ( NTP4VCStrictLowerBound A B C D E ) $.
ntp4vc-equal-ranges-syntax
  $a wff ( NTP4VCEqualRanges A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.
ntp4vc-max-uint32-def $a |- NTP4VCMaxUint32 =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 5 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.

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

${
  $d x A B C D $.
  ntp4vc-havoc-def $a |- ( NTP4VCHavoc A B C D ) =
    (
      x e. NTP4VCAddr |->
        if
        (
          ( NTP4VCSeparated x 1 C D ) ,
          ( B ` x ) ,
          ( A ` x )
        )
    ) $.
$}

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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-count-def $a |- ( NTP4VCCount A B C D E F ) =
  ( ( ( ( ( A ` B ) ` C ) ` D ) ` E ) ` F ) $.

${
  $d x y A B C D $.
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
  $d x A B C D E $.
  ntp4vc-unchanged-def $a |- (
    ( NTP4VCUnchanged A B C D E )
    <->
    A. x e. ZZ
      (
        D <_ x
        ->
        (
          x < E
          ->
          ( B ` ( NTP4VCShift C x ) )
          =
          ( A ` ( NTP4VCShift C x ) )
        )
      )
  ) $.
$}

${
  $d x A B C D E F $.
  ntp4vc-multiset-unchanged-def $a |- (
    ( NTP4VCMultisetUnchanged A B C D E F )
    <->
    A. x e. ZZ
      (
        ( NTP4VCSint32 x )
        ->
        (
          ( NTP4VCCount F B C D E x )
          =
          ( NTP4VCCount F A C D E x )
        )
      )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-upper-bound-def $a |- (
    ( NTP4VCUpperBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          ( A ` ( NTP4VCShift B x ) ) <_ E
        )
      )
  ) $.
$}

${
  $d x A B C D E $.
  ntp4vc-strict-lower-bound-def $a |- (
    ( NTP4VCStrictLowerBound A B C D E )
    <->
    A. x e. ZZ
      (
        C <_ x
        ->
        (
          x < D
          ->
          E < ( A ` ( NTP4VCShift B x ) )
        )
      )
  ) $.
$}

${
  $d x A B C D E F $.
  ntp4vc-equal-ranges-def $a |- (
    ( NTP4VCEqualRanges A B C D E F )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < ( E - D )
          ->
          (
            B ` ( NTP4VCShift ( NTP4VCShift C D ) x )
          )
          =
          (
            A ` ( NTP4VCShift ( NTP4VCShift C F ) x )
          )
        )
      )
  ) $.
$}

ntp4vc-x1-def $a |- ( NTP4VCX1 A B ) = ( A - B ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A ) = ( 1 + A ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) = ( ( 1 + A ) - B ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D E ) =
  ( ( NTP4VCA4 A B C D ) ` ( NTP4VCA2 C E ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F G ) =
  (
    NTP4VCHavoc
      A
      ( NTP4VCA4 B C D E )
      ( NTP4VCA3 D G )
      ( NTP4VCX3 F G )
  ) $.

${
  $d x y p m n v A B C D E F G H I J K L $.

  $( Source parameters:
     A=i_2, B=i_1, C=a, D=t_1, E=t_3, F=i, G=t_2, H=t.
     I is region, J is the extension of linked, K is to_uint32, and L is
     l_count_1'. The source let-bound objects are the explicit NTP4VCX*
     and NTP4VCA* definitions above. $)

  ntp4vc-i2-integer $e |- A e. ZZ $.
  ntp4vc-i1-integer $e |- B e. ZZ $.
  ntp4vc-a-address $e |- C e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-t2-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- L e.
    (
      (
        (
          (
            ( ZZ ^m ZZ )
            ^m
            ZZ
          )
          ^m
          ZZ
        )
        ^m
        NTP4VCAddr
      )
      ^m
      ( ZZ ^m NTP4VCAddr )
    ) $.

  ntp4vc-to-uint32-range $e |- A. x e. ZZ
    ( NTP4VCUint32 ( K ` x ) ) $.

  ntp4vc-to-uint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint32 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-count-section-empty $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                n <_ m
                ->
                (
                  ( NTP4VCSint32 v )
                  ->
                  ( NTP4VCCount L x p m n v ) = 0
                )
              ) $.

  ntp4vc-count-section-hit $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift p ( n - 1 ) ) ) = v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      1 + ( NTP4VCCount L x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount L x p m n v )
                  )
                )
              ) $.

  ntp4vc-count-section-miss $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. p e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift p ( n - 1 ) ) ) =/= v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      ( NTP4VCCount L x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount L x p m n v )
                    )
                  )
                )
              ) $.

  ntp4vc-count-section-read $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. ( ZZ ^m NTP4VCAddr )
        A. p e. NTP4VCAddr
          A. m e. ZZ
            A. n e. ZZ
              A. v e. ZZ
                (
                  ( NTP4VCSint32 v )
                  ->
                  (
                    ( NTP4VCUnchanged x y p m n )
                    ->
                    (
                      ( NTP4VCCount L y p m n v )
                      =
                      ( NTP4VCCount L x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i2-le-i $e |- A <_ F $.
  ntp4vc-i1-nonnegative $e |- 0 <_ B $.
  ntp4vc-i2-nonnegative $e |- 0 <_ A $.
  ntp4vc-i2-lt-i $e |- A < F $.
  ntp4vc-i1-le-i2 $e |- B <_ A $.
  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase C ) ) <_ 0 $.
  ntp4vc-i2-max-index $e |- A <_ NTP4VCMaxIndex $.
  ntp4vc-i2-relative-bound $e |- A <_ ( NTP4VCMaxUint32 + B ) $.
  ntp4vc-x1-conversion-bound $e |- (
    ( K ` ( NTP4VCX1 A B ) ) <_ NTP4VCMaxIndex
  ) $.
  ntp4vc-linked-allocation $e |- H e. J $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 B ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-x2-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX2 A ) ) $.

  ntp4vc-prefix-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA1 C ) A
  ) $.
  ntp4vc-current-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA2 C A ) 1
  ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA1 C ) F
  ) $.
  ntp4vc-shifted-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA3 C B ) ( NTP4VCX3 A B )
  ) $.
  ntp4vc-selected-value-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 D E C F A )
  ) $.

  ntp4vc-prefix-sorted $e |- (
    NTP4VCSorted ( NTP4VCA4 D E C F ) C 0 A
  ) $.
  ntp4vc-suffix-unchanged $e |- (
    NTP4VCUnchanged ( NTP4VCA4 D E C F ) E C A F
  ) $.
  ntp4vc-prefix-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA4 D E C F ) E C 0 A L
  ) $.
  ntp4vc-prefix-upper-bound $e |- (
    NTP4VCUpperBound
      ( NTP4VCA4 D E C F )
      C
      0
      B
      ( NTP4VCA5 D E C F A )
  ) $.
  ntp4vc-middle-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound
      ( NTP4VCA4 D E C F )
      C
      B
      A
      ( NTP4VCA5 D E C F A )
  ) $.
  ntp4vc-first-equal-range $e |- (
    NTP4VCEqualRanges
      ( NTP4VCA6 G D E C F A B )
      ( NTP4VCA4 D E C F )
      ( NTP4VCA3 C B )
      0
      ( NTP4VCX1 A B )
      1
  ) $.
  ntp4vc-second-equal-range $e |- (
    NTP4VCEqualRanges
      ( NTP4VCA6 G D E C F A B )
      ( NTP4VCA4 D E C F )
      ( NTP4VCA3 C B )
      ( NTP4VCX1 A B )
      ( NTP4VCX3 A B )
      0
  ) $.

  ntp4vc-insertion-sort-loop-inv-sorted-preserved-goal6 $a |- (
    NTP4VCSorted
      ( NTP4VCA6 G D E C F A B )
      C
      0
      ( NTP4VCX2 A )
  ) $.
$}
