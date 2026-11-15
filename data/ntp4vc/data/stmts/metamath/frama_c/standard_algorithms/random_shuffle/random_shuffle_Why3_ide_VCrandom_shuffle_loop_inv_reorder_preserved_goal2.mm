$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/random_shuffle/random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_reorder_preserved_goal2:
  the random-shuffle loop-invariant preservation condition states that two
  memory updates preserve the multiset of signed 32-bit values in the
  extended shuffled prefix, under the generated bounds, region, linking,
  unsigned- and signed-range, write-validity, unchanged-range, and prior
  multiset assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories remain arbitrary total functions from addresses
  to integers. NTP4VCShift, NTP4VCUpdate, NTP4VCSeparated, NTP4VCHavoc,
  NTP4VCValidRW, NTP4VCSint32, NTP4VCUint32, NTP4VCUnchanged, and
  NTP4VCMultisetUnchanged directly expand the corresponding source
  definitions. Every integer quantifier retains the full source domain ZZ.

  The arbitrary map I represents region, membership of allocation map H in
  the arbitrary set J represents linked, K represents to_uint32, L represents
  to_sint32, and the curried map M represents l_count_1'. The source range
  and identity laws for both conversion maps, the to_sint32-to_uint32
  compatibility law, and all four source counting laws are retained as
  universally quantified scoped hypotheses.

  The source let bindings a_1 through a_8 are retained by explicit
  definitions, including the ordered pair of full-domain updates in a_6.
  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift NTP4VCUpdate
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCUnchanged NTP4VCMultisetUnchanged NTP4VCCount
  NTP4VCA1 NTP4VCA2 NTP4VCA3 NTP4VCA4
  NTP4VCA5 NTP4VCA6 NTP4VCA7 NTP4VCA8
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-a1-class $a class ( NTP4VCA1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A B C D ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D E ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F G H ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F G H ) $.
ntp4vc-a8-class $a class ( NTP4VCA8 A B C D E F ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-count-def $a |- ( NTP4VCCount A B C D E F ) =
  ( ( ( ( ( A ` B ) ` C ) ` D ) ` E ) ` F ) $.

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

ntp4vc-a1-def $a |- ( NTP4VCA1 A ) =
  ( NTP4VCShift A 0 ) $.

ntp4vc-a2-def $a |- ( NTP4VCA2 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA1 C ) D ) $.

ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) =
  ( NTP4VCShift A B ) $.

ntp4vc-a4-def $a |- ( NTP4VCA4 A B C ) =
  ( NTP4VCShift A ( C ` ( 1 + B ) ) ) $.

ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D E ) =
  ( ( NTP4VCA2 A B C D ) ` ( NTP4VCA3 C E ) ) $.

ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F G H ) =
  (
    NTP4VCUpdate
      (
        NTP4VCUpdate
          ( NTP4VCA2 A B C D )
          ( NTP4VCA3 C E )
          G
      )
      ( NTP4VCA4 C F H )
      ( NTP4VCA5 A B C D E )
  ) $.

ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F G H ) =
  (
    ( NTP4VCA6 A B C D E F G H )
    `
    ( NTP4VCA3 C E )
  ) $.

ntp4vc-a8-def $a |- ( NTP4VCA8 A B C D E F ) =
  (
    ( NTP4VCA2 A B C D )
    `
    ( NTP4VCA4 C E F )
  ) $.

${
  $d x y p m n v A B C D E F G H I J K L M $.

  $( Source parameters:
     A=a, B=t_1, C=t_2, D=i_2, E=i_3, F=i_1, G=i, and H=t.
     I is region, J is the extension of linked, K is to_uint32, L is
     to_sint32, and M is l_count_1'. The source let-bound objects are the
     explicit NTP4VCA1 through NTP4VCA8 definitions above. $)

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
  ntp4vc-to-uint32-map $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-to-sint32-map $e |- L e. ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- M e.
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

  ntp4vc-to-sint32-range $e |- A. x e. ZZ
    ( NTP4VCSint32 ( L ` x ) ) $.

  ntp4vc-to-sint32-identity $e |- A. x e. ZZ
    (
      ( NTP4VCSint32 x )
      ->
      ( L ` x ) = x
    ) $.

  ntp4vc-to-sint32-uint32-compatibility $e |- A. x e. ZZ
    ( ( L ` ( K ` x ) ) = ( L ` x ) ) $.

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
                  ( NTP4VCCount M x p m n v ) = 0
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
                      1 + ( NTP4VCCount M x p m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount M x p m n v )
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
                      ( NTP4VCCount M x p m ( n - 1 ) v )
                      =
                      ( NTP4VCCount M x p m n v )
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
                      ( NTP4VCCount M y p m n v )
                      =
                      ( NTP4VCCount M x p m n v )
                    )
                  )
                ) $.

  ntp4vc-updated-read-equality $e |- (
    ( NTP4VCA7 B C A D E F G K )
    =
    ( NTP4VCA8 B C A D F K )
  ) $.
  ntp4vc-i2-positive $e |- 0 < D $.
  ntp4vc-i3-positive $e |- 0 < E $.
  ntp4vc-i1-nonnegative $e |- 0 <_ F $.
  ntp4vc-i1-lt-i3 $e |- F < E $.
  ntp4vc-i3-le-i2 $e |- E <_ D $.
  ntp4vc-i3-lt-i2 $e |- E < D $.
  ntp4vc-region-a $e |- ( I ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- H e. J $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 D ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA1 A ) D
  ) $.
  ntp4vc-i3-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA3 A E ) 1
  ) $.
  ntp4vc-a5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 B C A D E )
  ) $.
  ntp4vc-a8-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA8 B C A D F K )
  ) $.
  ntp4vc-i1-successor-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA4 A F K ) 1
  ) $.
  ntp4vc-a7-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA7 B C A D E F G K )
  ) $.
  ntp4vc-suffix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA2 B C A D )
      C
      A
      E
      D
  ) $.
  ntp4vc-prefix-multiset-unchanged $e |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA2 B C A D )
      C
      A
      0
      E
      M
  ) $.

  ntp4vc-random-shuffle-loop-inv-reorder-preserved-goal2 $a |- (
    NTP4VCMultisetUnchanged
      ( NTP4VCA6 B C A D E F G K )
      C
      A
      0
      ( K ` ( 1 + E ) )
      M
  ) $.
$}
