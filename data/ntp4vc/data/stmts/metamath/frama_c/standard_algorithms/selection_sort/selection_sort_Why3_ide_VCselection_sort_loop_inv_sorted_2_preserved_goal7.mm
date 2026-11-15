$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_loop_inv_sorted_2_preserved_goal7:
  the selection-sort loop-invariant preservation condition states that after
  swapping the current position with the selected minimum, the placed value
  is a lower bound for every value in the remaining half-open array suffix,
  under the generated bounds, memory-validity, sortedness, minimum,
  order-bound, unchanged-range, and multiset assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRD,
  NTP4VCValidRW, NTP4VCSint32, NTP4VCUint32, NTP4VCSorted,
  NTP4VCLowerBound, NTP4VCStrictLowerBound, NTP4VCUnchanged,
  NTP4VCMultisetUnchanged, and NTP4VCMinElement directly expand the
  corresponding source definitions. Every integer quantifier retains the
  full source domain ZZ, and every memory is an arbitrary total function
  from addresses to integers.

  The arbitrary map I represents the source region operation; membership of
  H in the arbitrary set J represents linked. The curried map K represents
  l_count_1', and all four source counting laws are retained as universally
  quantified scoped hypotheses. The source let bindings a_1 through a_9 and
  x, x_2, and x_3 are retained by explicit definitions. NTP4VCA6 expands
  the two source function updates in their original order.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCMaxIndex NTP4VCMaxUint32
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCSorted NTP4VCLowerBound NTP4VCStrictLowerBound
  NTP4VCUnchanged NTP4VCMultisetUnchanged NTP4VCMinElement
  NTP4VCCount
  NTP4VCX NTP4VCX2 NTP4VCX3
  NTP4VCA1 NTP4VCA2 NTP4VCA3 NTP4VCA4 NTP4VCA5
  NTP4VCA6 NTP4VCA7 NTP4VCA8 NTP4VCA9
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

ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B ) $.
ntp4vc-x3-class $a class ( NTP4VCX3 A B ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D E ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F G ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F G ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B C D E ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B C D E ) $.

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
ntp4vc-lower-bound-syntax
  $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-strict-lower-bound-syntax
  $a wff ( NTP4VCStrictLowerBound A B C D E ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.
ntp4vc-min-element-syntax
  $a wff ( NTP4VCMinElement A B C D ) $.

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
    A. x e. ZZ
      A. y e. ZZ
        (
          y < D
          ->
          (
            C <_ x
            ->
            (
              x < y
              ->
              ( A ` ( NTP4VCShift B x ) )
              <_
              ( A ` ( NTP4VCShift B y ) )
            )
          )
        )
  ) $.
$}

${
  $d x A B C D E $.
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

ntp4vc-min-element-def $a |- (
  ( NTP4VCMinElement A B C D )
  <->
  (
    0 <_ D
    /\
    (
      D < C
      /\
      (
        NTP4VCLowerBound
          A B 0 C ( A ` ( NTP4VCShift B D ) )
      )
    )
  )
) $.

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( 1 + A ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B ) = ( A - B ) $.
ntp4vc-x3-def $a |- ( NTP4VCX3 A B ) = ( A - B ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D E ) =
  ( ( NTP4VCA2 A B C D ) ` ( NTP4VCA3 C E ) ) $.

${
  $d x A B C D E F G $.
  ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F G ) =
    (
      x e. NTP4VCAddr |->
        if
        (
          x = ( NTP4VCA4 C F ) ,
          ( NTP4VCA5 A B C D E ) ,
          if
          (
            x = ( NTP4VCA3 C E ) ,
            G ,
            ( ( NTP4VCA2 A B C D ) ` x )
          )
        )
    ) $.
$}

ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F G ) =
  (
    ( NTP4VCA6 A B C D E F G )
    ` ( NTP4VCA3 C E )
  ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B C D E ) =
  (
    ( NTP4VCA2 A B C D )
    ` ( NTP4VCA4 C E )
  ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B C D E ) =
  (
    ( NTP4VCA2 A B C D )
    ` ( NTP4VCShift C ( E - 1 ) )
  ) $.

${
  $d x y p m n v A B C D E F G H I J K $.

  $( Source parameters:
     A=a, B=t_1, C=t_2, D=i_2, E=i_3, F=i_1, G=i, and H=t.
     I is region, J is the extension of linked, and K is l_count_1'.
     The source let-bound objects are the explicit NTP4VCX* and NTP4VCA*
     definitions above. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- D e. ZZ $.
  ntp4vc-i3-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-i-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- J C_ ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- K e.
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
                  ( NTP4VCCount K x p m n v ) = 0
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
                      1 + ( NTP4VCCount K x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount K x p m n v )
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
                      ( NTP4VCCount K x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount K x p m n v )
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
                      ( NTP4VCCount K y p m n v )
                      =
                      ( NTP4VCCount K x p m n v )
                    )
                  )
                ) $.

  ntp4vc-swap-readback $e |- (
    ( NTP4VCA7 B C A D E F G )
    =
    ( NTP4VCA8 B C A D F )
  ) $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-lt-i2 $e |- F < D $.
  ntp4vc-i3-le-i1 $e |- E <_ F $.
  ntp4vc-i1-le-i2 $e |- F <_ D $.
  ntp4vc-i3-le-i2 $e |- E <_ D $.
  ntp4vc-i3-nonnegative $e |- 0 <_ E $.
  ntp4vc-i3-lt-i2 $e |- E < D $.
  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-i3-max-index $e |- E <_ NTP4VCMaxIndex $.
  ntp4vc-i1-max-uint32 $e |- F <_ NTP4VCMaxUint32 $.
  ntp4vc-i2-relative-bound $e |- D <_ ( NTP4VCMaxUint32 + E ) $.
  ntp4vc-linked-allocation $e |- H e. J $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-x-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX E )
  ) $.
  ntp4vc-x2-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX2 F E )
  ) $.
  ntp4vc-t2-minus-one-sint32 $e |- (
    NTP4VCSint32 ( C ` ( NTP4VCShift A ( -u 1 ) ) )
  ) $.
  ntp4vc-array-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA1 A ) D
  ) $.
  ntp4vc-suffix-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA3 A E ) ( NTP4VCX3 D E )
  ) $.
  ntp4vc-a8-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA8 B C A D F )
  ) $.
  ntp4vc-a5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 B C A D E )
  ) $.
  ntp4vc-a9-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA9 B C A D E )
  ) $.
  ntp4vc-prefix-sorted $e |- (
    NTP4VCSorted ( NTP4VCA2 B C A D ) A 0 E
  ) $.
  ntp4vc-a7-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA7 B C A D E F G )
  ) $.
  ntp4vc-prior-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA2 B C A D ) C A 0 D K
  ) $.
  ntp4vc-selected-minimum $e |- (
    NTP4VCMinElement
      ( NTP4VCA2 B C A D )
      ( NTP4VCA3 A E )
      ( NTP4VCX3 D E )
      ( NTP4VCX2 F E )
  ) $.
  ntp4vc-selected-strict-lower-bound $e |- (
    NTP4VCStrictLowerBound
      ( NTP4VCA2 B C A D )
      ( NTP4VCA3 A E )
      0
      ( NTP4VCX2 F E )
      ( NTP4VCA8 B C A D F )
  ) $.
  ntp4vc-prefix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA6 B C A D E F G )
      ( NTP4VCA2 B C A D )
      A
      0
      E
  ) $.
  ntp4vc-after-selected-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA6 B C A D E F G )
      ( NTP4VCA2 B C A D )
      A
      ( 1 + F )
      D
  ) $.
  ntp4vc-between-current-and-selected-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA6 B C A D E F G )
      ( NTP4VCA2 B C A D )
      A
      ( NTP4VCX E )
      F
  ) $.
  ntp4vc-predecessor-lower-bound $e |- (
    0 < E
    ->
    (
      NTP4VCLowerBound
        ( NTP4VCA2 B C A D )
        A
        E
        D
        ( NTP4VCA9 B C A D E )
    )
  ) $.

  ntp4vc-selection-sort-loop-inv-sorted-2-preserved-goal7 $a |- (
    NTP4VCLowerBound
      ( NTP4VCA6 B C A D E F G )
      A
      ( NTP4VCX E )
      D
      ( NTP4VCA7 B C A D E F G )
  ) $.
$}
