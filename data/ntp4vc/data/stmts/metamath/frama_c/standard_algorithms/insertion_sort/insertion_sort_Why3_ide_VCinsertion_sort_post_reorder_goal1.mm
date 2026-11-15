$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_post_reorder_goal1:
  the insertion-sort post-reorder verification condition states that the
  prefix through i_1 has the same multiset of signed 32-bit values after a
  havoc update of that prefix, under the generated index, region, linking,
  integer-range, memory-validity, sortedness, unchanged-range, and prior
  multiset assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRW,
  NTP4VCUint32, NTP4VCSorted, NTP4VCUnchanged, and
  NTP4VCMultisetUnchanged directly expand the corresponding source
  definitions. Every integer quantifier retains the full source domain ZZ,
  and every memory is an arbitrary total function from addresses to integers.

  The arbitrary map G represents region, membership of the allocation map F
  in the arbitrary set H represents linked, and the curried map I represents
  l_count_1'. The four imported counting laws are retained as universally
  quantified scoped hypotheses. The source let-bound a_1 and a_2 are expanded
  at their uses. Splitting the source implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc NTP4VCUint32Limit
  NTP4VCValidRW NTP4VCUint32 NTP4VCSorted NTP4VCUnchanged
  NTP4VCMultisetUnchanged NTP4VCCount
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sorted-syntax
  $a wff ( NTP4VCSorted A B C D ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
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
        (
          -u ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
          <_
          x
          /\
          x
          <
          ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
        )
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
  $d x y p m n v A B C D E F G H I $.

  $( Source parameters:
     A=a, B=t_1, C=t_2, D=i, E=i_1, and F=t.
     G is region, H is the extension of linked, and I is l_count_1'.
     The source lets are expanded as a_1=shift(A,0) and
     a_2=havoc(B,C,a_1,D). $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- B e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-allocation-map $e |- F e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- H C_ ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- I e.
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
                  (
                    -u ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                    <_
                    v
                    /\
                    v
                    <
                    ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                  )
                  ->
                  ( NTP4VCCount I x p m n v ) = 0
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
                    (
                      -u ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                      <_
                      v
                      /\
                      v
                      <
                      ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                    )
                    ->
                    (
                      1 + ( NTP4VCCount I x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount I x p m n v )
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
                    (
                      -u ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                      <_
                      v
                      /\
                      v
                      <
                      ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                    )
                    ->
                    (
                      ( NTP4VCCount I x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount I x p m n v )
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
                  (
                    -u ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                    <_
                    v
                    /\
                    v
                    <
                    ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8
                  )
                  ->
                  (
                    ( NTP4VCUnchanged x y p m n )
                    ->
                    (
                      ( NTP4VCCount I y p m n v )
                      =
                      ( NTP4VCCount I x p m n v )
                    )
                  )
                ) $.

  ntp4vc-i1-le-i $e |- E <_ D $.
  ntp4vc-i1-nonnegative $e |- 0 <_ E $.
  ntp4vc-i-le-i1 $e |- D <_ E $.
  ntp4vc-region-a $e |- ( G ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- F e. H $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW F ( NTP4VCShift A 0 ) D
  ) $.
  ntp4vc-prefix-sorted $e |- (
    NTP4VCSorted
      ( NTP4VCHavoc B C ( NTP4VCShift A 0 ) D )
      A
      0
      E
  ) $.
  ntp4vc-middle-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCHavoc B C ( NTP4VCShift A 0 ) D )
      C
      A
      E
      D
  ) $.
  ntp4vc-prefix-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCHavoc B C ( NTP4VCShift A 0 ) D )
      C
      A
      0
      E
      I
  ) $.

  ntp4vc-insertion-sort-post-reorder-goal1 $a |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCHavoc B C ( NTP4VCShift A 0 ) E )
      C
      A
      0
      E
      I
  ) $.
$}
