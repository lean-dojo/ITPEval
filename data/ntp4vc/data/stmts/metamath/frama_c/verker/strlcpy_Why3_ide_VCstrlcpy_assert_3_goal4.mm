$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/strlcpy_Why3_ide_VCstrlcpy_assert_3_goal4: the strlcpy
  verification condition concludes that the updated destination string has
  length i_1, under the generated unsigned-range, source-termination,
  memory-validity, linking, constancy, branch, no-earlier-null, and copied-
  prefix assumptions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCValidRD, NTP4VCValidRW,
  NTP4VCSeparated, NTP4VCSint8, NTP4VCUint64, and NTP4VCValidStr directly
  expand the corresponding source definitions. NTP4VCHavoc is fixed
  pointwise by havoc_access, and NTP4VCUpdate is full-domain functional
  update.

  The arbitrary integer-valued map H represents region. Membership of the
  allocation map G in the arbitrary set I represents linked, while membership
  of the source memory C in the arbitrary set J represents sconst. K
  represents to_uint64 and L represents l_strlen; their source range,
  identity, and fixed-point laws are retained explicitly without assigning
  stronger properties to either symbol.

  Every source let-binding is expanded at its uses. All addresses, integers,
  maps, predicates, and quantified indices retain their unrestricted source
  domains. The existential null-position witnesses in both valid-string
  assumptions remain internal, and both prefix assumptions retain their full
  integer quantifier domains and implication scopes. The source Boolean
  branch is represented by its equivalent pair of implications for the
  complementary integer cases F <= strlen and strlen < F. Splitting the
  source curried implication chain into scoped essential hypotheses is
  bidirectionally equivalent for the arbitrary displayed parameters. The
  final declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCSint8Limit NTP4VCUint64Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated
  NTP4VCSint8 NTP4VCUint64 NTP4VCValidStr
  NTP4VCHavoc NTP4VCUpdate NTP4VCStrlen
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-sint8-limit-class $a class NTP4VCSint8Limit $.
ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-strlen-class $a class ( NTP4VCStrlen A B C ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint8-syntax $a wff ( NTP4VCSint8 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.
ntp4vc-valid-str-syntax $a wff ( NTP4VCValidStr A B C ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-sint8-limit-def $a |- NTP4VCSint8Limit = ; ; 1 2 8 $.
ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.
ntp4vc-shift-def $a |- ( NTP4VCShift A B ) =
  <. ( NTP4VCBase A ) , ( ( NTP4VCOffset A ) + B ) >. $.
ntp4vc-strlen-def $a |- ( NTP4VCStrlen A B C ) =
  ( A ` <. B , C >. ) $.

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

ntp4vc-sint8-def $a |- ( ( NTP4VCSint8 A ) <->
  ( -u NTP4VCSint8Limit <_ A /\ A < NTP4VCSint8Limit )
) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
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

${
  $d x A B C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

${
  $d x y A B C $.
  ntp4vc-valid-str-def $a |- ( ( NTP4VCValidStr A B C ) <->
    E. x e. ZZ
      (
        ( B ` ( NTP4VCShift C x ) ) = 0
        /\
        (
          ( NTP4VCUint64 x )
          /\
          (
            ( NTP4VCValidRW A ( NTP4VCShift C 0 ) ( 1 + x ) )
            /\
            A. y e. ZZ
              (
                y <_ x
                ->
                ( NTP4VCSint8 ( B ` ( NTP4VCShift C y ) ) )
              )
          )
        )
      )
  ) $.
$}

${
  $d x y A B C D E F G H I J K L $.

  $( Source parameters:
     A=a_1, B=a, C=t_2, D=t_1, E=i_1, F=i, and G=t.
     H is region; I and J are the linked and sconst extensions; K is
     to_uint64; and L is l_strlen. Source lets are expanded as:
       x=base(A), x_1=base(B), x_2=strlen(L,C,B),
       a_2=shift(A,0), a_3=havoc(D,C,shift(A,0),E), and
       a_4=update(a_3,shift(A,E),0). $)

  ntp4vc-a1-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a-address $e |- B e. NTP4VCAddr $.
  ntp4vc-t2-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-t1-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i1-integer $e |- E e. ZZ $.
  ntp4vc-i-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-sconst-predicate $e |- J C_ ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-to-uint64-function $e |- K e. ( ZZ ^m ZZ ) $.
  ntp4vc-strlen-function $e |- L e.
    ( ZZ ^m ( ( ZZ ^m NTP4VCAddr ) X. NTP4VCAddr ) ) $.

  ntp4vc-to-uint64-range $e |- A. x e. ZZ
    ( NTP4VCUint64 ( K ` x ) ) $.

  ntp4vc-to-uint64-identity $e |- A. x e. ZZ
    (
      ( NTP4VCUint64 x )
      ->
      ( K ` x ) = x
    ) $.

  ntp4vc-strlen-fixed-point $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        (
          ( NTP4VCStrlen L x y )
          =
          if
          (
            ( x ` ( NTP4VCShift y 0 ) ) = 0 ,
            0 ,
            ( K ` ( 1 + ( NTP4VCStrlen L x ( NTP4VCShift y 1 ) ) ) )
          )
        ) $.

  ntp4vc-strlen-range $e |-
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        ( NTP4VCUint64 ( NTP4VCStrlen L x y ) ) $.

  ntp4vc-i-nonzero $e |- F =/= 0 $.

  ntp4vc-distinct-bases $e |- (
    ( NTP4VCBase A ) =/= ( NTP4VCBase B )
  ) $.

  ntp4vc-source-end-null $e |- (
    (
      C
      `
      ( NTP4VCShift B ( NTP4VCStrlen L C B ) )
    )
    =
    0
  ) $.

  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( H ` ( NTP4VCBase A ) ) <_ 0 $.

  ntp4vc-linked-allocation $e |- G e. I $.
  ntp4vc-sconst-source $e |- C e. J $.

  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 F ) $.
  ntp4vc-i1-uint64 $e |- ( NTP4VCUint64 E ) $.

  ntp4vc-source-valid-string $e |- ( NTP4VCValidStr G C B ) $.

  ntp4vc-source-length-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCStrlen L C B )
  ) $.

  ntp4vc-source-prefix-valid-rd $e |- (
    NTP4VCValidRD G ( NTP4VCShift B 0 ) E
  ) $.

  ntp4vc-destination-i-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCShift A 0 ) F
  ) $.

  ntp4vc-destination-i1-valid-rw $e |- (
    NTP4VCValidRW G ( NTP4VCShift A 0 ) E
  ) $.

  ntp4vc-updated-destination-valid-string $e |- (
    NTP4VCValidStr
      G
      (
        NTP4VCUpdate
          ( NTP4VCHavoc D C ( NTP4VCShift A 0 ) E )
          ( NTP4VCShift A E )
          0
      )
      A
  ) $.

  ntp4vc-branch-result $e |- (
    (
      F <_ ( NTP4VCStrlen L C B )
      ->
      ( K ` ( F - 1 ) ) = E
    )
    /\
    (
      ( NTP4VCStrlen L C B ) < F
      ->
      ( NTP4VCStrlen L C B ) = E
    )
  ) $.

  ntp4vc-no-null-before-source-end $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < ( NTP4VCStrlen L C B )
        ->
        ( C ` ( NTP4VCShift B x ) ) =/= 0
      )
    ) $.

  ntp4vc-copied-prefix $e |- A. x e. ZZ
    (
      0 <_ x
      ->
      (
        x < E
        ->
        (
          (
            NTP4VCHavoc D C ( NTP4VCShift A 0 ) E
          )
          `
          ( NTP4VCShift A x )
        )
        =
        (
          (
            NTP4VCHavoc D C ( NTP4VCShift A 0 ) E
          )
          `
          ( NTP4VCShift B x )
        )
      )
    ) $.

  ntp4vc-strlcpy-assert-3-goal4 $a |- (
    NTP4VCStrlen
      L
      (
        NTP4VCUpdate
          ( NTP4VCHavoc D C ( NTP4VCShift A 0 ) E )
          ( NTP4VCShift A E )
          0
      )
      A
  )
  =
  E $.
$}
