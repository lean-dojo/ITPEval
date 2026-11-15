$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/standard_algorithms/partial_sum/partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14:
  the partial-sum verification condition establishes the signed 32-bit upper
  bound for adding the next input value to the preceding partial sum, under
  the generated index, accumulation-bound, memory-validity, separation,
  unchanged-memory, partial-sum, region, and linking assumptions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Addresses are represented exactly by ZZ X. ZZ, with base and offset given
  by 1st and 2nd. NTP4VCShift, NTP4VCUpdate, NTP4VCHavoc,
  NTP4VCValidRD, NTP4VCValidRW, NTP4VCSeparated, NTP4VCSint32, and
  NTP4VCUint32 directly expand the corresponding source definitions.

  NTP4VCUnchanged, NTP4VCAccumulateBounds, and NTP4VCPartialSum expand the
  three quantified source predicates over the full integer domain.
  NTP4VCAccumulate is the curried source l_accumulate_1' operation. Its
  signed-range, empty-range, successor, and unchanged-memory laws are retained
  as explicit scoped hypotheses. The arbitrary map H represents region,
  membership of G in I represents linked, and J is the source to_uint32 map
  with its range and identity laws.

  The source let-bound values a_2 through a_7, x, and x_1 are retained by
  explicit conservative definitions. Splitting the source implication chain
  into displayed hypotheses is bidirectionally equivalent for the arbitrary
  displayed parameters. The final declaration is Metamath's native unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCAddr NTP4VCBase NTP4VCOffset NTP4VCShift
  NTP4VCUpdate NTP4VCHavoc
  NTP4VCMaxSint32 NTP4VCSint32Limit NTP4VCUint32Limit
  NTP4VCValidRD NTP4VCValidRW NTP4VCSeparated
  NTP4VCSint32 NTP4VCUint32
  NTP4VCAccumulate NTP4VCUnchanged
  NTP4VCAccumulateBounds NTP4VCPartialSum
  NTP4VCToUint32Laws
  NTP4VCAccumulateRange NTP4VCAccumulateEmpty
  NTP4VCAccumulateNext NTP4VCAccumulateRead
  NTP4VCA2 NTP4VCA3 NTP4VCX NTP4VCA4
  NTP4VCX1 NTP4VCA5 NTP4VCA6 NTP4VCA7
$.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-max-sint32-class $a class NTP4VCMaxSint32 $.
ntp4vc-sint32-limit-class $a class NTP4VCSint32Limit $.
ntp4vc-uint32-limit-class $a class NTP4VCUint32Limit $.

ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.
ntp4vc-shift-class $a class ( NTP4VCShift A B ) $.
ntp4vc-update-class $a class ( NTP4VCUpdate A B C ) $.
ntp4vc-havoc-class $a class ( NTP4VCHavoc A B C D ) $.
ntp4vc-accumulate-class
  $a class ( NTP4VCAccumulate A B C D E ) $.

ntp4vc-valid-rd-syntax $a wff ( NTP4VCValidRD A B C ) $.
ntp4vc-valid-rw-syntax $a wff ( NTP4VCValidRW A B C ) $.
ntp4vc-separated-syntax $a wff ( NTP4VCSeparated A B C D ) $.
ntp4vc-sint32-syntax $a wff ( NTP4VCSint32 A ) $.
ntp4vc-uint32-syntax $a wff ( NTP4VCUint32 A ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-accumulate-bounds-syntax
  $a wff ( NTP4VCAccumulateBounds A B C D E ) $.
ntp4vc-partial-sum-syntax
  $a wff ( NTP4VCPartialSum A B C D E ) $.
ntp4vc-to-uint32-laws-syntax
  $a wff ( NTP4VCToUint32Laws A ) $.
ntp4vc-accumulate-range-syntax
  $a wff ( NTP4VCAccumulateRange A ) $.
ntp4vc-accumulate-empty-syntax
  $a wff ( NTP4VCAccumulateEmpty A ) $.
ntp4vc-accumulate-next-syntax
  $a wff ( NTP4VCAccumulateNext A ) $.
ntp4vc-accumulate-read-syntax
  $a wff ( NTP4VCAccumulateRead A ) $.

ntp4vc-a2-class $a class ( NTP4VCA2 A ) $.
ntp4vc-a3-class $a class ( NTP4VCA3 A ) $.
ntp4vc-x-class $a class ( NTP4VCX A B ) $.
ntp4vc-a4-class $a class ( NTP4VCA4 A B C D E ) $.
ntp4vc-x1-class $a class ( NTP4VCX1 A ) $.
ntp4vc-a5-class $a class ( NTP4VCA5 A B C D E F ) $.
ntp4vc-a6-class $a class ( NTP4VCA6 A B C D E F ) $.
ntp4vc-a7-class $a class ( NTP4VCA7 A B C D E F G ) $.

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

${
  $d x A $.  $d x B $.  $d x C $.
  ntp4vc-update-def $a |- ( NTP4VCUpdate A B C ) =
    (
      x e. NTP4VCAddr |->
        if ( x = B , C , ( A ` x ) )
    ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.
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

ntp4vc-accumulate-def $a |- (
  NTP4VCAccumulate A B C D E
) = ( ( ( ( A ` B ) ` C ) ` D ) ` E ) $.

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

ntp4vc-sint32-def $a |- ( ( NTP4VCSint32 A ) <->
  ( -u NTP4VCSint32Limit <_ A /\ A < NTP4VCSint32Limit )
) $.

ntp4vc-uint32-def $a |- ( ( NTP4VCUint32 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint32Limit )
) $.

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
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
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  ntp4vc-accumulate-bounds-def $a |- (
    ( NTP4VCAccumulateBounds A B C D E )
    <->
    A. x e. ZZ
      (
        x <_ D
        ->
        (
          0 <_ x
          ->
          (
            -u NTP4VCSint32Limit
            <_
            ( NTP4VCAccumulate A B C x E )
            /\
            (
              ( NTP4VCAccumulate A B C x E )
              <_
              NTP4VCMaxSint32
            )
          )
        )
      )
  ) $.
$}

${
  $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x E $.
  ntp4vc-partial-sum-def $a |- (
    ( NTP4VCPartialSum A B C D E )
    <->
    A. x e. ZZ
      (
        0 <_ x
        ->
        (
          x < D
          ->
          (
            ( B ` ( NTP4VCShift E x ) )
            =
            ( NTP4VCAccumulate A B C ( 1 + x ) 0 )
          )
        )
      )
  ) $.
$}

${
  $d x A $.
  ntp4vc-to-uint32-laws-def $a |- (
    ( NTP4VCToUint32Laws A )
    <->
    (
      A. x e. ZZ ( NTP4VCUint32 ( A ` x ) )
      /\
      A. x e. ZZ
        (
          ( NTP4VCUint32 x )
          ->
          ( A ` x ) = x
        )
    )
  ) $.
$}

${
  $d x y z u $.
  $d x A $.  $d y A $.  $d z A $.  $d u A $.
  ntp4vc-accumulate-range-def $a |- (
    ( NTP4VCAccumulateRange A )
    <->
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          A. u e. ZZ
            ( NTP4VCSint32 ( NTP4VCAccumulate A x y z u ) )
  ) $.
$}

${
  $d x y z u $.
  $d x A $.  $d y A $.  $d z A $.  $d u A $.
  ntp4vc-accumulate-empty-def $a |- (
    ( NTP4VCAccumulateEmpty A )
    <->
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          A. u e. ZZ
            (
              z <_ 0
              ->
              (
                ( NTP4VCSint32 u )
                ->
                ( NTP4VCAccumulate A x y z u ) = u
              )
            )
  ) $.
$}

${
  $d x y z u $.
  $d x A $.  $d y A $.  $d z A $.  $d u A $.
  ntp4vc-accumulate-next-def $a |- (
    ( NTP4VCAccumulateNext A )
    <->
    A. x e. ( ZZ ^m NTP4VCAddr )
      A. y e. NTP4VCAddr
        A. z e. ZZ
          A. u e. ZZ
            (
              0 < z
              ->
              (
                ( NTP4VCSint32 u )
                ->
                (
                  (
                    ( x ` ( NTP4VCShift y ( z - 1 ) ) )
                    +
                    ( NTP4VCAccumulate A x y ( z - 1 ) u )
                  )
                  =
                  ( NTP4VCAccumulate A x y z u )
                )
              )
            )
  ) $.
$}

${
  $d x y z u v $.
  $d x A $.  $d y A $.  $d z A $.  $d u A $.  $d v A $.
  ntp4vc-accumulate-read-def $a |- (
    ( NTP4VCAccumulateRead A )
    <->
    A. u e. ZZ
      A. x e. ( ZZ ^m NTP4VCAddr )
        A. y e. ( ZZ ^m NTP4VCAddr )
          A. z e. NTP4VCAddr
            A. v e. ZZ
              (
                ( NTP4VCSint32 u )
                ->
                (
                  ( NTP4VCUnchanged x y z 0 v )
                  ->
                  (
                    ( NTP4VCAccumulate A y z v u )
                    =
                    ( NTP4VCAccumulate A x z v u )
                  )
                )
              )
  ) $.
$}

ntp4vc-a2-def $a |- ( NTP4VCA2 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-a3-def $a |- ( NTP4VCA3 A ) = ( NTP4VCShift A 0 ) $.
ntp4vc-x-def $a |- ( NTP4VCX A B ) = ( A ` ( NTP4VCA3 B ) ) $.

ntp4vc-a4-def $a |- ( NTP4VCA4 A B C D E ) =
  (
    NTP4VCHavoc
      A
      ( NTP4VCUpdate B ( NTP4VCA2 C ) ( NTP4VCX B D ) )
      ( NTP4VCShift C 1 )
      ( E - 1 )
  ) $.

ntp4vc-x1-def $a |- ( NTP4VCX1 A ) = ( A - 1 ) $.

ntp4vc-a5-def $a |- ( NTP4VCA5 A B C D E F ) =
  (
    ( NTP4VCA4 A B C D E )
    `
    ( NTP4VCShift C ( NTP4VCX1 F ) )
  ) $.

ntp4vc-a6-def $a |- ( NTP4VCA6 A B C D E F ) =
  (
    ( NTP4VCA4 A B C D E )
    `
    ( NTP4VCShift D F )
  ) $.

ntp4vc-a7-def $a |- ( NTP4VCA7 A B C D E F G ) =
  (
    ( NTP4VCA4 A B C D E )
    `
    ( NTP4VCShift C ( G ` ( NTP4VCX1 F ) ) )
  ) $.

${
  $( Source parameters:
     A=a, B=a_1, C=t_2, D=t_1, E=i, F=i_1, and G=t.
     H is region, I is the extension of linked, J is to_uint32, and K is
     l_accumulate_1'. $)

  ntp4vc-a-address $e |- A e. NTP4VCAddr $.
  ntp4vc-a1-address $e |- B e. NTP4VCAddr $.
  ntp4vc-new-memory $e |- C e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-old-memory $e |- D e. ( ZZ ^m NTP4VCAddr ) $.
  ntp4vc-i-integer $e |- E e. ZZ $.
  ntp4vc-i1-integer $e |- F e. ZZ $.
  ntp4vc-allocation-map $e |- G e. ( ZZ ^m ZZ ) $.

  ntp4vc-region-map $e |- H e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- I C_ ( ZZ ^m ZZ ) $.
  ntp4vc-to-uint32-map $e |- J e. ( ZZ ^m ZZ ) $.
  ntp4vc-accumulate-map $e |- K e.
    (
      (
        (
          ( ZZ ^m ZZ )
          ^m
          ZZ
        )
        ^m
        NTP4VCAddr
      )
      ^m
      ( ZZ ^m NTP4VCAddr )
    ) $.

  ntp4vc-to-uint32-laws $e |- ( NTP4VCToUint32Laws J ) $.
  ntp4vc-accumulate-range $e |- ( NTP4VCAccumulateRange K ) $.
  ntp4vc-accumulate-empty $e |- ( NTP4VCAccumulateEmpty K ) $.
  ntp4vc-accumulate-next $e |- ( NTP4VCAccumulateNext K ) $.
  ntp4vc-accumulate-read $e |- ( NTP4VCAccumulateRead K ) $.

  ntp4vc-a5-accumulate $e |- (
    ( NTP4VCA5 D C A B E F )
    =
    (
      NTP4VCAccumulate
        K
        ( NTP4VCA4 D C A B E )
        B
        F
        0
    )
  ) $.

  ntp4vc-i-positive $e |- 0 < E $.
  ntp4vc-i1-positive $e |- 0 < F $.
  ntp4vc-i1-le-i $e |- F <_ E $.
  ntp4vc-i1-lt-i $e |- F < E $.

  ntp4vc-region-a $e |- ( H ` ( NTP4VCBase A ) ) <_ 0 $.
  ntp4vc-region-a1 $e |- ( H ` ( NTP4VCBase B ) ) <_ 0 $.
  ntp4vc-linked-allocation $e |- G e. I $.

  ntp4vc-i-uint32 $e |- ( NTP4VCUint32 E ) $.
  ntp4vc-i1-uint32 $e |- ( NTP4VCUint32 F ) $.
  ntp4vc-x-sint32 $e |- ( NTP4VCSint32 ( NTP4VCX C B ) ) $.

  ntp4vc-a3-valid-rd-one $e |- (
    NTP4VCValidRD G ( NTP4VCA3 B ) 1
  ) $.

  ntp4vc-a3-valid-rd-i $e |- (
    NTP4VCValidRD G ( NTP4VCA3 B ) E
  ) $.

  ntp4vc-a2-valid-rw-one $e |- (
    NTP4VCValidRW G ( NTP4VCA2 A ) 1
  ) $.

  ntp4vc-a2-valid-rw-i $e |- (
    NTP4VCValidRW G ( NTP4VCA2 A ) E
  ) $.

  ntp4vc-accumulate-bounds $e |- (
    NTP4VCAccumulateBounds K C B ( 1 + E ) 0
  ) $.

  ntp4vc-separated-input-output $e |- (
    NTP4VCSeparated ( NTP4VCA3 B ) E ( NTP4VCA2 A ) E
  ) $.

  ntp4vc-a6-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA6 D C A B E F )
  ) $.

  ntp4vc-a5-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA5 D C A B E F )
  ) $.

  ntp4vc-a7-sint32 $e |- (
    NTP4VCSint32 ( NTP4VCA7 D C A B E F J )
  ) $.

  ntp4vc-unchanged-input $e |- (
    NTP4VCUnchanged
      ( NTP4VCA4 D C A B E )
      C
      B
      0
      E
  ) $.

  ntp4vc-partial-sum $e |- (
    NTP4VCPartialSum
      K
      ( NTP4VCA4 D C A B E )
      B
      F
      A
  ) $.

  ntp4vc-partial-sum-assert-rte-signed-overflow-2-goal14 $a |- (
    (
      ( NTP4VCA6 D C A B E F )
      +
      ( NTP4VCA7 D C A B E F J )
    )
    <_
    NTP4VCMaxSint32
  ) $.
$}
