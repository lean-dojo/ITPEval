$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/remove_copy/remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5:
  the remove-copy loop-invariant preservation condition states that the
  branch-updated destination prefix retains the multiplicity of every signed
  32-bit value other than the removed value, under the generated counting,
  range, memory-validity, separation, linking, absence, and unchanged-range
  assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. Memories remain arbitrary total functions from addresses to
  integers. NTP4VCShift, NTP4VCUpdate, NTP4VCSeparated, NTP4VCHavoc,
  NTP4VCValidRD, NTP4VCValidRW, NTP4VCSint32, NTP4VCUint32,
  NTP4VCHasValue, NTP4VCUnchanged, NTP4VCCount, and
  NTP4VCMultisetRetainRest directly render the corresponding source
  definitions. Every integer quantifier retains the full source domain ZZ.

  The source Boolean p is represented by the exactly two-element carrier
  { 0 , 1 }, with false represented by 0. The arbitrary map N represents
  region, membership of allocation map H in the arbitrary set O represents
  linked, and the curried map P represents l_count_1'. All four source
  counting laws are retained as universally quantified scoped hypotheses.
  The source let bindings are named by NTP4VCX through NTP4VCA7 and preserve
  their original dependency order.

  The proposition-valued source if is represented by its equivalent guarded
  disjunction: equality conjoined with the then-branch, or inequality
  conjoined with the else-branch. Splitting the source curried implication
  chain into scoped essential hypotheses is bidirectionally equivalent for
  the arbitrary displayed parameters. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUpdate NTP4VCSeparated NTP4VCHavoc
  NTP4VCSint32Limit NTP4VCUint32Limit NTP4VCMaxIndex
  NTP4VCValidRD NTP4VCValidRW NTP4VCSint32 NTP4VCUint32
  NTP4VCHasValue NTP4VCUnchanged NTP4VCCount
  NTP4VCMultisetRetainRest
  NTP4VCX NTP4VCX1 NTP4VCA2 NTP4VCA3 NTP4VCA4
  NTP4VCX2 NTP4VCA5 NTP4VCA6 NTP4VCA7
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-max-index-class $a class NTP4VCMaxIndex $.
ntp4vc-count-class $a class ( NTP4VCCount A B C D E F ) $.

ntp4vc-x-class $a class ( NTP4VCX A B C D E ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A ) $.
ntp4vc-x2-class $a class ( NTP4VCX2 A B C D E ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F ) $.

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
ntp4vc-has-value-syntax
  $a wff ( NTP4VCHasValue A B C D E ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-multiset-retain-rest-syntax
  $a wff ( NTP4VCMultisetRetainRest A B C D E F G H I J ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-max-index-def $a |- NTP4VCMaxIndex =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 4 $.

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
  $d x A B C D E $.
  ntp4vc-has-value-def $a |- (
    ( NTP4VCHasValue A B C D E )
    <->
    E. x e. ZZ
      (
        ( A ` ( NTP4VCShift B x ) ) = E
        /\
        ( C <_ x /\ x < D )
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
  $d x A B C D E F G H I J $.
  ntp4vc-multiset-retain-rest-def $a |- (
    ( NTP4VCMultisetRetainRest A B C D E F G H I J )
    <->
    A. x e. ZZ
      (
        x =/= I
        ->
        (
          ( NTP4VCSint32 x )
          ->
          (
            ( NTP4VCCount J B C D E x )
            =
            ( NTP4VCCount J A F G H x )
          )
        )
      )
  ) $.
$}

ntp4vc-x-def $a |- ( NTP4VCX A B C D E ) =
  ( NTP4VCCount E A B 0 C D ) $.
ntp4vc-x1-def $a |- ( NTP4VCX1 A ) = ( 1 + A ) $.
ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A B ) = ( NTP4VCShift A B ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-x2-def $a |- ( NTP4VCX2 A B C D E ) =
  ( C - ( NTP4VCX A B C D E ) ) $.
ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA4 C ) D ) $.
ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F ) =
  (
    ( NTP4VCA5 E A D F )
    `
    ( NTP4VCA3 B C )
  ) $.
ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F ) =
  (
    NTP4VCShift
      D
      ( NTP4VCX2 A B C E F )
  ) $.

${
  $d x y q m n v A B C D E F G H I J K L M N O P $.

  $( Source parameters:
     A=t_3, B=a_1, C=i_5, D=i, E=a, F=t_1, G=i_2, H=t,
     I=i_1, J=i_3, K=i_4, L=t_2, and M=p.
     N is region, O is the extension of linked, and P is l_count_1'.
     Source lets are:
       x=count(P,A,B,0,C,D), x_1=1+C, a_2=shift(B,0),
       a_3=shift(B,C), a_4=shift(E,0), x_2=C-x,
       a_5=havoc(F,A,a_4,G), a_6=a_5(a_3), and a_7=shift(E,x_2). $)

  ntp4vc-t3-memory $e |- A e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-i5-integer $e |- C e. ZZ $.
  ntp4vc-i-integer $e |- D e. ZZ $.
  ntp4vc-a-address $e |- E e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- F e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- G e. ZZ $.
  ntp4vc-allocation-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-i1-integer $e |- I e. ZZ $.
  ntp4vc-i3-integer $e |- J e. ZZ $.
  ntp4vc-i4-integer $e |- K e. ZZ $.
  ntp4vc-t2-memory $e |- L e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-p-boolean $e |- M e. { 0 , 1 } $.

  ntp4vc-region-map $e |- N e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- O C_ ( ZZ ^m ZZ ) $.
  ntp4vc-count-map $e |- P e.
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
      A. q e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                n <_ m
                ->
                (
                  ( NTP4VCSint32 v )
                  ->
                  ( NTP4VCCount P x q m n v ) = 0
                )
              ) $.

  ntp4vc-count-section-hit $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. q e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift q ( n - 1 ) ) ) = v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      1 + ( NTP4VCCount P x q m ( n - 1 ) v )
                    )
                    =
                    ( NTP4VCCount P x q m n v )
                  )
                )
              ) $.

  ntp4vc-count-section-miss $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. q e. NTP4VCAddr
        A. m e. ZZ
          A. n e. ZZ
            A. v e. ZZ
              (
                ( x ` ( NTP4VCShift q ( n - 1 ) ) ) =/= v
                ->
                (
                  m < n
                  ->
                  (
                    ( NTP4VCSint32 v )
                    ->
                    (
                      ( NTP4VCCount P x q m ( n - 1 ) v )
                      =
                      ( NTP4VCCount P x q m n v )
                    )
                  )
                )
              ) $.

  ntp4vc-count-section-read $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. ( ZZ ^m NTP4VCAddr )
        A. q e. NTP4VCAddr
          A. m e. ZZ
            A. n e. ZZ
              A. v e. ZZ
                (
                  ( NTP4VCSint32 v )
                  ->
                  (
                    ( NTP4VCUnchanged x y q m n )
                    ->
                    (
                      ( NTP4VCCount P y q m n v )
                      =
                      ( NTP4VCCount P x q m n v )
                    )
                  )
                ) $.

  ntp4vc-i5-le-i2 $e |- C <_ G $.
  ntp4vc-i5-lt-i2 $e |- C < G $.
  ntp4vc-region-a $e |- ( N ` ( NTP4VCBase E ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( N ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-count-le-i5 $e |- ( NTP4VCX A B C D P ) <_ C $.
  ntp4vc-count-nonnegative $e |- 0 <_ ( NTP4VCX A B C D P ) $.
  ntp4vc-i5-max-index $e |- C <_ NTP4VCMaxIndex $.
  ntp4vc-linked-allocation $e |- H e. O $.

  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 I ) $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 G ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 J ) $.
  ntp4vc-i4-uint32 $e |- ( NTP4VCUint32 K ) $.
  ntp4vc-i5-uint32 $e |- ( NTP4VCUint32 C ) $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 D ) $.
  ntp4vc-x1-uint32 $e |- ( NTP4VCUint32 ( NTP4VCX1 C ) ) $.

  ntp4vc-source-prefix-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA2 B ) G
  ) $.
  ntp4vc-current-source-valid-rd $e |- (
    NTP4VCValidRD H ( NTP4VCA3 B C ) 1
  ) $.
  ntp4vc-destination-prefix-valid-rw $e |- (
    NTP4VCValidRW H ( NTP4VCA4 E ) G
  ) $.
  ntp4vc-source-destination-separated $e |- (
    NTP4VCSeparated ( NTP4VCA2 B ) G E 1
  ) $.

  ntp4vc-x2-uint32 $e |- (
    NTP4VCUint32 ( NTP4VCX2 A B C D P )
  ) $.
  ntp4vc-a6-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA6 A B C E F G )
  ) $.
  ntp4vc-no-removed-value-in-destination $e |- -.
    (
      NTP4VCHasValue
        ( NTP4VCA5 F A E G )
        E
        0
        ( NTP4VCX2 A B C D P )
        D
    ) $.
  ntp4vc-source-suffix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA5 F A E G )
      A
      B
      C
      G
  ) $.
  ntp4vc-destination-suffix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA5 F A E G )
      A
      E
      ( NTP4VCX2 A B C D P )
      G
  ) $.
  ntp4vc-prefix-retains-other-values $e |- (
    NTP4VCMultisetRetainRest
      ( NTP4VCA5 F A E G )
      A
      B
      0
      C
      E
      0
      ( NTP4VCX2 A B C D P )
      D
      P
  ) $.

  ntp4vc-loop-branch $e |- (
    (
      ( NTP4VCA6 A B C E F G ) = D
      /\
      (
        ( NTP4VCA5 F A E G ) = L
        /\
        (
          K
          +
          (
            NTP4VCCount
              P
              A
              B
              0
              C
              ( L ` ( NTP4VCA3 B C ) )
          )
        )
        =
        C
      )
    )
    \/
    (
      ( NTP4VCA6 A B C E F G ) =/= D
      /\
      (
        M = 0
        /\
        (
          J = I
          /\
          (
            ( I + ( NTP4VCX A B C D P ) ) = C
            /\
            (
              ( J + ( NTP4VCX A B C D P ) ) = C
              /\
              (
                ( K + ( NTP4VCX A B C D P ) ) = ( NTP4VCX1 C )
                /\
                (
                  (
                    NTP4VCUpdate
                      ( NTP4VCA5 F A E G )
                      ( NTP4VCA7 A B C E D P )
                      ( NTP4VCA6 A B C E F G )
                  )
                  =
                  L
                  /\
                  (
                    C <_ ( NTP4VCMaxIndex + ( NTP4VCX A B C D P ) )
                    /\
                    (
                      NTP4VCValidRW
                        H
                        ( NTP4VCA7 A B C E D P )
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
  ) $.

  ntp4vc-remove-copy-loop-inv-retain-preserved-goal5 $a |- (
    NTP4VCMultisetRetainRest
      L
      A
      B
      0
      ( NTP4VCX1 C )
      E
      0
      K
      D
      P
  ) $.
$}
