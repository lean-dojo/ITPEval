$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/replace_copy/replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0:
  the replace-copy postcondition states that, under the generated integer
  bounds, memory-validity, separation, unchanged-suffix, and replacement-prefix
  assumptions, reducing the havoc range to the completed prefix preserves the
  replacement predicate on that prefix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCSeparated, NTP4VCHavoc,
  NTP4VCValidRD, NTP4VCValidRW, NTP4VCUint32, NTP4VCSint32,
  NTP4VCUnchanged, and NTP4VCReplace directly expand the corresponding source
  definitions. Every integer quantifier retains the full source domain ZZ,
  and every memory is an arbitrary total function from addresses to integers.

  The arbitrary map J represents the source region function, and membership
  of the allocation map G in the arbitrary set K represents linked. No
  additional laws are imposed on either symbol. The source let-bound
  addresses a_2 and a_3 and memory a_4 are retained by explicit definitions.

  Splitting the source curried implication chain into scoped essential
  hypotheses is bidirectionally equivalent for the arbitrary displayed
  parameters. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSeparated NTP4VCHavoc
  NTP4VCUint32Limit NTP4VCSint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCUint32 NTP4VCSint32
  NTP4VCUnchanged NTP4VCReplace
  NTP4VCA2 NTP4VCA3 NTP4VCA4
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D ) $.

ntp4vc-separated-syntax
  $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-valid-rd-syntax
  $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax
  $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-uint32-syntax
  $a wff ( NTP4VCUint32 A ) $.
ntp4vc-sint32-syntax
  $a wff ( NTP4VCSint32 A ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-replace-syntax
  $a wff ( NTP4VCReplace A B C D E F G ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-uint32-limit-def $a |- NTP4VCUint32Limit =
  ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 6 $.
ntp4vc-sint32-limit-def $a |- NTP4VCSint32Limit =
  ; ; ; ; ; ; ; ; ; 2 1 4 7 4 8 3 6 4 8 $.

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

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

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
  $d x A B C D E F G $.
  ntp4vc-replace-def $a |- (
    ( NTP4VCReplace A B C D E F G )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < D
          ->
          (
            (
              ( B ` ( NTP4VCShift C x ) ) = F
              ->
              ( A ` ( NTP4VCShift E x ) ) = G
            )
            /\
            (
              ( B ` ( NTP4VCShift C x ) ) =/= F
              ->
              ( A ` ( NTP4VCShift E x ) )
              =
              ( B ` ( NTP4VCShift C x ) )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D ) =
  ( NTP4VCHavoc A B ( NTP4VCA3 C ) D ) $.

${
  $d x A B C D E F G H I J K $.

  $( Source parameters:
     A=a_1, B=a, C=t_1, D=t_2, E=i_2, F=i_3, G=t, H=i,
     and I=i_1. J is region and K is the extension of linked. The source
     lets are NTP4VCA2(A)=shift(A,0), NTP4VCA3(B)=shift(B,0), and
     NTP4VCA4(C,D,B,E)=havoc(C,D,NTP4VCA3(B),E). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t1-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t2-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i2-integer $e |- E e. ZZ $.
  ntp4vc-i3-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-i-integer $e |- H e. ZZ $.
  ntp4vc-i1-integer $e |- I e. ZZ $.

  ntp4vc-region-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- K C_ ( ZZ ^m ZZ ) $.

  ntp4vc-i3-le-i2 $e |- F <_ E $.
  ntp4vc-i3-nonnegative $e |- 0 <_ F $.
  ntp4vc-i2-le-i3 $e |- E <_ F $.
  ntp4vc-region-a $e |- ( J ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( J ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- G e. K $.
  ntp4vc-i2-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i3-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-i-sint32 $e |- ( NTP4VCSint32 H ) $.
  ntp4vc-i1-sint32 $e |- ( NTP4VCSint32 I ) $.

  ntp4vc-prefix-valid-rd $e |- (
    NTP4VCValidRD G ( NTP4VCA2 A ) E
  ) $.

  ntp4vc-prefix-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCA3 B ) E
  ) $.

  ntp4vc-source-destination-separated $e |- (
    NTP4VCSeparated ( NTP4VCA2 A ) E B 1
  ) $.

  ntp4vc-suffix-unchanged $e |- (
    NTP4VCUnchanged
      ( NTP4VCA4 C D B E )
      D
      A
      F
      E
  ) $.

  ntp4vc-completed-prefix-replaced $e |- (
    NTP4VCReplace
      ( NTP4VCA4 C D B E )
      D
      A
      F
      B
      I
      H
  ) $.

  ntp4vc-replace-copy-post-replace-goal0 $a |- (
    NTP4VCReplace
      ( NTP4VCHavoc C D ( NTP4VCA3 B ) F )
      D
      A
      F
      B
      I
      H
  ) $.
$}
