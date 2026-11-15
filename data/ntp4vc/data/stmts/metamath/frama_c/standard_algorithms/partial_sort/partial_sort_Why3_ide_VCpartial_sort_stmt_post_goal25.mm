$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_stmt_post_goal25:
  the partial-sort statement-post verification condition states that the
  final havoced memory preserves the multiset of the original memory over
  the half-open prefix ending at i_2 + 1, under the generated integer,
  memory-validity, heap, bound, unchanged-range, multiset, signed-32,
  unsigned-32, region, and linking assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories are arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCUint32, NTP4VCIsHeap, NTP4VCUnchanged,
  NTP4VCMultisetUnchanged, NTP4VCUpperBound, NTP4VCLowerBound, and
  NTP4VCMaxElement directly expand the corresponding source definitions.
  NTP4VCTDiv is truncating integer division toward zero.

  The arbitrary map J represents region, membership of the allocation map I
  in the arbitrary set K represents linked, and the curried map L represents
  l_count_1'. All four source counting laws are retained as universally
  quantified scoped hypotheses. Every source let-bound object a_1 through
  a_8 and x is retained by an explicit definition. Every integer quantifier
  retains the full source domain ZZ.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCValidRD NTP4VCValidRW
  NTP4VCSint32 NTP4VCUint32 NTP4VCIsHeap NTP4VCUnchanged
  NTP4VCMultisetUnchanged NTP4VCUpperBound NTP4VCLowerBound
  NTP4VCMaxElement NTP4VCCount
  NTP4VCA1 NTP4VCA2 NTP4VCA3 NTP4VCA4 NTP4VCX
  NTP4VCA5 NTP4VCA6 NTP4VCA7 NTP4VCA8 NTP4VCA9
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-is-heap-syntax $a wff ( NTP4VCIsHeap A B C ) $.
ntp4vc-unchanged-syntax $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.
ntp4vc-upper-bound-syntax $a wff ( NTP4VCUpperBound A B C D E ) $.
ntp4vc-lower-bound-syntax $a wff ( NTP4VCLowerBound A B C D E ) $.
ntp4vc-max-element-syntax $a wff ( NTP4VCMaxElement A B C D ) $.

ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B C D E F ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D E F G ) $.
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F G ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B ) $.
ntp4vc-a9-class $a class ( NTP4VCA9 A B C D E F G ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
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

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
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
  $d x A B C $.
  ntp4vc-is-heap-def $a |- (
    ( NTP4VCIsHeap A B C )
    <->
    A. x e. ZZ
      (
        0 < x
        ->
        (
          x < C
          ->
          (
            ( A ` ( NTP4VCShift B x ) )
            <_
            (
              A
              `
              (
                NTP4VCShift
                  B
                  ( NTP4VCTDiv ( x - 1 ) 2 )
              )
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

ntp4vc-max-element-def $a |- (
  ( NTP4VCMaxElement A B C D )
  <->
  (
    0 <_ D
    /\
    (
      D < C
      /\
      (
        NTP4VCUpperBound
          A B 0 C ( A ` ( NTP4VCShift B D ) )
      )
    )
  )
) $.

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B C D E F ) =
  ( NTP4VCHavoc A ( NTP4VCA2 B C D E ) ( NTP4VCA1 D ) F ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D E F G ) =
  (
    NTP4VCHavoc
      A
      ( NTP4VCA3 B C D E F G )
      ( NTP4VCA1 E )
      F
  ) $.
ntp4vc-x-def $a |- ( NTP4VCX A ) = ( A - 1 ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B ) =
  ( NTP4VCShift A ( NTP4VCX B ) ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F G ) =
  (
    ( NTP4VCA4 A B C D E F G )
    `
    ( NTP4VCA5 E F )
  ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F ) =
  (
    ( NTP4VCA3 A B C D E F )
    `
    ( NTP4VCA1 D )
  ) $.
ntp4vc-a8-def $a |- ( NTP4VCA8 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a9-def $a |- ( NTP4VCA9 A B C D E F G ) =
  (
    ( NTP4VCA3 A B C D E F )
    `
    ( NTP4VCA8 D G )
  ) $.

${
  $d x y p m n v A B C D E F G H I J K L $.

  $( Source parameters:
     A=a, B=t_1, C=t_4, D=i_1, E=t_2, F=i, G=t_3,
     H=i_2, and I=t. J is region, K is the extension of linked,
     and L is l_count_1'. The source let-bound objects are the explicit
     NTP4VCA*, and NTP4VCX definitions above. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t4-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- D e. ZZ $.
  ntp4vc-t2-memory $e |- E e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-t3-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- H e. ZZ $.
  ntp4vc-allocation-map $e |- I e. ( ZZ ^m ZZ ) $.
  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.
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

  ntp4vc-a6-equals-a7 $e |- (
    ( NTP4VCA6 G E B C A D F )
    =
    ( NTP4VCA7 E B C A D F )
  ) $.
  ntp4vc-i1-positive $e |- 0 < D $.
  ntp4vc-i1-le-i $e |- D <_ F $.
  ntp4vc-i2-le-i $e |- H <_ F $.
  ntp4vc-i1-nonnegative $e |- 0 <_ D $.
  ntp4vc-i2-lt-i $e |- H < F $.
  ntp4vc-i1-le-i2 $e |- D <_ H $.
  ntp4vc-region-a $e |- ( J ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-a9-lt-a7 $e |- (
    ( NTP4VCA9 E B C A D F H )
    <
    ( NTP4VCA7 E B C A D F )
  ) $.
  ntp4vc-linked-allocation $e |- I e. K $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 H ) $.
  ntp4vc-a1-valid-rd $e |- (
    NTP4VCValidRD I ( NTP4VCA1 A ) 1
  ) $.
  ntp4vc-a8-valid-rd $e |- (
    NTP4VCValidRD I ( NTP4VCA8 A H ) 1
  ) $.
  ntp4vc-a1-i-valid-rw $e |- (
    NTP4VCValidRW I ( NTP4VCA1 A ) F
  ) $.
  ntp4vc-a1-i1-valid-rw $e |- (
    NTP4VCValidRW I ( NTP4VCA1 A ) D
  ) $.
  ntp4vc-a2-is-heap $e |- (
    NTP4VCIsHeap ( NTP4VCA2 B C A D ) A D
  ) $.
  ntp4vc-a2-t4-multiset $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA2 B C A D ) C A 0 D L
  ) $.
  ntp4vc-a7-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA7 E B C A D F )
  ) $.
  ntp4vc-a9-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA9 E B C A D F H )
  ) $.
  ntp4vc-a3-is-heap $e |- (
    NTP4VCIsHeap ( NTP4VCA3 E B C A D F ) A D
  ) $.
  ntp4vc-a3-t4-multiset $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA3 E B C A D F ) C A 0 H L
  ) $.
  ntp4vc-a3-t4-unchanged $e |- (
    NTP4VCUnchanged ( NTP4VCA3 E B C A D F ) C A H F
  ) $.
  ntp4vc-a3-upper-bound $e |- (
    NTP4VCUpperBound
      ( NTP4VCA3 E B C A D F )
      A 0 D
      ( NTP4VCA7 E B C A D F )
  ) $.
  ntp4vc-a3-lower-bound $e |- (
    NTP4VCLowerBound
      ( NTP4VCA3 E B C A D F )
      A D H
      ( NTP4VCA7 E B C A D F )
  ) $.
  ntp4vc-a6-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA6 G E B C A D F )
  ) $.
  ntp4vc-a4-is-heap $e |- (
    NTP4VCIsHeap
      ( NTP4VCA4 G E B C A D F )
      A
      ( NTP4VCX D )
  ) $.
  ntp4vc-a4-a3-multiset $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA4 G E B C A D F )
      ( NTP4VCA3 E B C A D F )
      A 0 D L
  ) $.
  ntp4vc-a4-max-element $e |- (
    NTP4VCMaxElement
      ( NTP4VCA4 G E B C A D F )
      A D ( NTP4VCX D )
  ) $.

  ntp4vc-partial-sort-stmt-post-goal25 $a |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA4 G E B C A D F )
      C A 0 ( 1 + H ) L
  ) $.
$}
