$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/make_heap/make_heap_Why3_ide_VCmake_heap_post_reorder_goal1:
  the make-heap post-reorder verification condition states that the final
  prefix has the same multiset of signed 32-bit values as the preceding
  memory, under the generated region, linking, integer-range, memory-validity,
  conditional havoc, heap, prior multiset, and unchanged-range assumptions.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCHavoc, NTP4VCValidRW,
  NTP4VCSint32, NTP4VCUint32, NTP4VCIsHeap, NTP4VCUnchanged, and
  NTP4VCMultisetUnchanged directly expand the corresponding source
  definitions. NTP4VCTDiv is truncating integer division toward zero.
  Every integer quantifier retains the full source domain ZZ, and every
  memory is an arbitrary total function from addresses to integers.

  The source Boolean p is represented by the exactly two-element carrier
  { 0 , 1 }, with false represented by 0. The arbitrary map I represents
  region, membership of the allocation map C in the arbitrary set J
  represents linked, and the curried map K represents l_count_1'. All four
  source counting laws are retained as universally quantified scoped
  hypotheses. The source let bindings a_1 and x are retained by explicit
  definitions.

  The proposition-valued if is rendered by the equivalent guarded
  disjunction (condition and then-branch) or (negated condition and
  else-branch). Splitting the source curried implication chain into scoped
  essential hypotheses is bidirectionally equivalent for the arbitrary
  displayed parameters. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCTDiv NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCIsHeap NTP4VCUnchanged NTP4VCMultisetUnchanged
  NTP4VCCount NTP4VCX NTP4VCA1
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
ntp4vc-x-class $a class ( NTP4VCX A ) $.
ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-is-heap-syntax
  $a wff ( NTP4VCIsHeap A B C ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-unchanged-syntax
  $a wff ( NTP4VCMultisetUnchanged A B C D E F ) $.

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

ntp4vc-x-def $a |- ( NTP4VCX A ) = ( 1 + A ) $.
ntp4vc-a1-def $a |- ( NTP4VCA1 A ) = ( NTP4VCShift A 0 ) $.

${
  $d x y p m n v A B C D E F G H I J K $.

  $( Source parameters:
     A=i_1, B=a, C=t, D=i, E=p, F=t_1, G=t_3, and H=t_2.
     I is region, J is the extension of linked, and K is l_count_1'.
     The source lets are NTP4VCA1(B)=shift(B,0) and NTP4VCX(A)=1+A. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- C e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-p-boolean $e |- E e. { 0 , 1 } $.
  ntp4vc-t1-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t3-memory $e |- G e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- H e. ( ZZ ^m NTP4VCAddr ) $.

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

  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- C e. J $.
  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 A ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW C ( NTP4VCA1 B ) D
  ) $.

  ntp4vc-reorder-branch $e |- (
    (
      0 < D
      /\
      (
        E = 0
        /\
        (
          ( NTP4VCHavoc F G ( NTP4VCA1 B ) D ) = H
          /\
          (
            0 < A
            /\
            (
              A <_ D
              /\
              (
                D <_ A
                /\
                (
                  ( NTP4VCIsHeap H B A )
                  /\
                  (
                    (
                      NTP4VCMultisetUnchanged
                        H
                        G
                        B
                        0
                        ( NTP4VCX A )
                        K
                    )
                    /\
                    (
                      NTP4VCUnchanged
                        H
                        G
                        B
                        ( NTP4VCX A )
                        D
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
      -. ( 0 < D )
      /\
      G = H
    )
  ) $.

  ntp4vc-make-heap-post-reorder-goal1 $a |- (
    NTP4VCMultisetUnchanged
      H
      G
      B
      0
      D
      K
  ) $.
$}
