$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/hillel_challenge_FulcrumNoOverflow_fulcrumqtvc: the fulcrum
  no-overflow verification condition accumulates signed 32-bit array sums in
  a two-word big-integer representation while maintaining a minimum
  prefix-versus-suffix difference. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Signed 32-bit words are represented exactly by the integer interval
  [-2^31,2^31), which is in bijection with the source BitVec 32 carrier and
  makes every source signed-value conversion the identity. The big-integer
  and array carriers remain arbitrary nonempty sets. Their q, r, v, element,
  and length accessors are arbitrary total functions subject to exactly the
  source invariant, extensionality, zero, and typing assumptions.

  NTP4VCSum is the half-open finite integer sum of signed array elements,
  definitionally realizing the source fc and int.Sum specifications.
  NTP4VCDiff is the source absolute difference between the prefix and suffix
  sums. The remaining named predicates are biconditional factorizations of
  the nested loop invariants, overflow checks, update obligations,
  proposition-valued conditional, and final minimum property. Expanding them
  recovers every source quantifier and implication; let-bound values are
  substituted definitionally. The final $a declaration is Metamath's native
  unproved statement encoding, and this database contains no $p declaration.
$)

$c
  NTP4VCIn32 NTP4VCBV32 NTP4VCAbs NTP4VCSum NTP4VCDiff
  NTP4VCWide NTP4VCBigRep NTP4VCCoordEq
  NTP4VCState NTP4VCFinal NTP4VCZeroFinal
  NTP4VCFullStep NTP4VCFullLoop NTP4VCBestPhase
  NTP4VCRightInv NTP4VCRightStep NTP4VCRightLoop
  NTP4VCFulcrum
$.

ntp4vc-in32-syntax $a wff ( NTP4VCIn32 A ) $.
ntp4vc-bv32-syntax $a class NTP4VCBV32 $.
ntp4vc-abs-syntax $a class ( NTP4VCAbs A ) $.
ntp4vc-sum-syntax $a class ( NTP4VCSum A B C D ) $.
ntp4vc-diff-syntax $a class ( NTP4VCDiff A B C D ) $.
ntp4vc-wide-syntax $a wff ( NTP4VCWide A ) $.
ntp4vc-big-rep-syntax
  $a wff ( NTP4VCBigRep A B C D ) $.
ntp4vc-coord-eq-syntax
  $a wff ( NTP4VCCoordEq A B C D E ) $.
ntp4vc-state-syntax
  $a wff ( NTP4VCState A B C D E F G H I ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B C D E ) $.
ntp4vc-zero-final-syntax
  $a wff ( NTP4VCZeroFinal A B C ) $.
ntp4vc-full-step-syntax
  $a wff ( NTP4VCFullStep A B C D E F G H I J K L ) $.
ntp4vc-full-loop-syntax
  $a wff ( NTP4VCFullLoop A B C D E F G H I J K L ) $.
ntp4vc-best-phase-syntax
  $a wff ( NTP4VCBestPhase A B C D E F G H I ) $.
ntp4vc-right-inv-syntax
  $a wff ( NTP4VCRightInv A B C D E F ) $.
ntp4vc-right-step-syntax
  $a wff ( NTP4VCRightStep A B C D E F G ) $.
ntp4vc-right-loop-syntax
  $a wff ( NTP4VCRightLoop A B C D E F G H I J ) $.
ntp4vc-fulcrum-syntax
  $a wff ( NTP4VCFulcrum A B C D E F G H ) $.

ntp4vc-in32-definition $a |- (
  NTP4VCIn32 A
) <-> (
  ( -u ( 2 ^ ; 3 1 ) ) <_ A
  /\
  A < ( 2 ^ ; 3 1 )
) $.

ntp4vc-bv32-definition $a |- NTP4VCBV32 = {
  x e. ZZ | ( NTP4VCIn32 x )
} $.

ntp4vc-abs-definition $a |- (
  NTP4VCAbs A
) = if (
  A < 0 ,
  ( -u A ) ,
  A
) $.

${
  $d k A B C D $.

  ntp4vc-sum-definition $a |- (
    NTP4VCSum A B C D
  ) = (
    sum_ k e. ( C ..^ D )
      ( A ` <. B , k >. )
  ) $.
$}

ntp4vc-diff-definition $a |- (
  NTP4VCDiff A B C D
) = (
  NTP4VCAbs
    (
      ( NTP4VCSum A C 0 D )
      -
      ( NTP4VCSum A C D ( B ` C ) )
    )
) $.

ntp4vc-wide-definition $a |- (
  NTP4VCWide A
) <-> (
  (
    -u
      (
        ( 2 ^ ; 3 1 )
        x.
        ( 2 ^ ; 3 1 )
      )
  ) <_ A
  /\
  A <_
    (
      (
        ( 2 ^ ; 3 1 )
        x.
        ( 2 ^ ; 3 1 )
      )
      -
      1
    )
) $.

ntp4vc-big-rep-definition $a |- (
  NTP4VCBigRep A B C D
) <-> (
  (
    ( -u ( 2 ^ ; 3 1 ) ) <_ ( A ` D )
    /\
    ( A ` D ) <_ ( ( 2 ^ ; 3 1 ) - 1 )
  )
  /\
  (
    (
      0 <_ ( B ` D )
      /\
      ( B ` D ) <_ ( ( 2 ^ ; 3 1 ) - 1 )
    )
    /\
    (
      ( C ` D )
      =
      (
        (
          ( A ` D )
          x.
          ( 2 ^ ; 3 1 )
        )
        +
        ( B ` D )
      )
    )
  )
) $.

ntp4vc-coord-eq-definition $a |- (
  NTP4VCCoordEq A B C D E
) <-> (
  ( C ` D ) = ( C ` E )
  /\
  (
    ( B ` D ) = ( B ` E )
    /\
    ( A ` D ) = ( A ` E )
  )
) $.

${
  $d j A B C D E F G H I $.

  ntp4vc-state-definition $a |- (
    NTP4VCState A B C D E F G H I
  ) <-> (
    ; 5 5 < ; 8 9
    /\
    (
      ( C ` E ) = ( NTP4VCSum A D 0 I )
      /\
      (
        ( C ` F ) =
          ( NTP4VCSum A D I ( B ` D ) )
        /\
        (
          (
            0 <_ G
            /\
            G <_ I
          )
          /\
          (
            ( C ` H ) = ( NTP4VCDiff A B D G )
            /\
            A. j e. ZZ
              (
                (
                  0 <_ j
                  /\
                  j <_ I
                )
                ->
                ( C ` H ) <_ ( NTP4VCDiff A B D j )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-final-definition $a |- (
    NTP4VCFinal A B C D E
  ) <-> (
    (
      0 <_ E
      /\
      E <_ ( B ` D )
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i <_ ( B ` D )
        )
        ->
        ( NTP4VCDiff A B D E )
        <_
        ( NTP4VCDiff A B D i )
      )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-zero-final-definition $a |- (
    NTP4VCZeroFinal A B C
  ) <-> (
    (
      0 <_ 0
      /\
      0 <_ ( B ` C )
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i <_ ( B ` C )
        )
        ->
        ( NTP4VCDiff A B C 0 )
        <_
        ( NTP4VCDiff A B C i )
      )
  ) $.
$}

${
  $d b d l o r A B C D E F G H I J K L $.

  ntp4vc-full-step-definition $a |- (
    NTP4VCFullStep A B C D E F G H I J K L
  ) <-> (
    (
      0 <_ L
      /\
      L < ( F ` G )
    )
    /\
    (
      (
        NTP4VCWide
          (
            ( D ` J )
            +
            ( E ` <. G , L >. )
          )
      )
      /\
      A. l e. A
        (
          ( D ` l )
          =
          (
            ( D ` J )
            +
            ( E ` <. G , L >. )
          )
          ->
          (
            (
              0 <_ L
              /\
              L < ( F ` G )
            )
            /\
            (
              (
                NTP4VCWide
                  (
                    ( D ` K )
                    -
                    ( E ` <. G , L >. )
                  )
              )
              /\
              A. r e. A
                (
                  ( D ` r )
                  =
                  (
                    ( D ` K )
                    -
                    ( E ` <. G , L >. )
                  )
                  ->
                  (
                    (
                      NTP4VCWide
                        (
                          NTP4VCAbs
                            (
                              ( D ` l )
                              -
                              ( D ` r )
                            )
                        )
                    )
                    /\
                    A. d e. A
                      (
                        ( D ` d )
                        =
                        (
                          NTP4VCAbs
                            (
                              ( D ` l )
                              -
                              ( D ` r )
                            )
                        )
                        ->
                        (
                          (
                            0 <_ ( D ` d )
                            /\
                            0 <_ ( D ` H )
                          )
                          /\
                          (
                            (
                              ( D ` d ) < ( D ` H )
                              ->
                              A. b e. A
                                (
                                  ( NTP4VCIn32 ( L + 1 ) )
                                  /\
                                  A. o e. NTP4VCBV32
                                    (
                                      o = ( L + 1 )
                                      ->
                                      (
                                        (
                                          NTP4VCBigRep B C D d
                                        )
                                        /\
                                        (
                                          (
                                            NTP4VCCoordEq
                                              B C D d b
                                          )
                                          ->
                                          (
                                            NTP4VCState
                                              E F D G l r o b
                                              ( L + 1 )
                                          )
                                        )
                                      )
                                    )
                                )
                            )
                            /\
                            (
                              -. ( D ` d ) < ( D ` H )
                              ->
                              (
                                NTP4VCState
                                  E F D G l r I H
                                  ( L + 1 )
                              )
                            )
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
$}

${
  $d i A B C D E F G H I J K L $.

  ntp4vc-full-loop-definition $a |- (
    NTP4VCFullLoop A B C D E F G H I J K L
  ) <-> (
    (
      A. i e. NTP4VCBV32
        (
          (
            (
              0 <_ i
              /\
              i <_ L
            )
            /\
            (
              NTP4VCState E F D G J K I H i
            )
          )
          ->
          (
            NTP4VCFullStep
              A B C D E F G H I J K i
          )
        )
    )
    /\
    (
      (
        NTP4VCState
          E F D G J K I H ( L + 1 )
      )
      ->
      ( NTP4VCFinal E F D G I )
    )
  ) $.
$}

${
  $d b d k l o r A B C D E F G H I $.

  ntp4vc-best-phase-definition $a |- (
    NTP4VCBestPhase A B C D E F G H I
  ) <-> (
    (
      NTP4VCWide
        (
          NTP4VCAbs
            (
              ( D ` E )
              -
              ( D ` I )
            )
        )
    )
    /\
    A. d e. A
      (
        ( D ` d )
        =
        (
          NTP4VCAbs
            (
              ( D ` E )
              -
              ( D ` I )
            )
        )
        ->
        (
          ( NTP4VCIn32 ( ( G ` H ) - 1 ) )
          /\
          A. o e. NTP4VCBV32
            (
              o = ( ( G ` H ) - 1 )
              ->
              (
                (
                  0 <_ ( o + 1 )
                  ->
                  (
                    (
                      NTP4VCState
                        F G D H E I 0 d 0
                    )
                    /\
                    A. b e. A
                      A. k e. NTP4VCBV32
                        A. l e. A
                          A. r e. A
                            (
                              NTP4VCFullLoop
                                A B C D F G H b k l r o
                            )
                  )
                )
                /\
                (
                  ( o + 1 ) < 0
                  ->
                  ( NTP4VCZeroFinal F G H )
                )
              )
            )
        )
      )
  ) $.
$}

ntp4vc-right-inv-definition $a |- (
  NTP4VCRightInv A B C D E F
) <-> (
  (
    0 <_ F
    /\
    F <_ E
  )
  /\
  (
    ; 5 5 < ; 8 9
    /\
    ( B ` D ) = ( NTP4VCSum A C 0 F )
  )
) $.

${
  $d r A B C D E F G $.

  ntp4vc-right-step-definition $a |- (
    NTP4VCRightStep A B C D E F G
  ) <-> (
    (
      0 <_ G
      /\
      G < ( E ` D )
    )
    /\
    (
      (
        NTP4VCWide
          (
            ( B ` F )
            +
            ( C ` <. D , G >. )
          )
      )
      /\
      A. r e. A
        (
          ( B ` r )
          =
          (
            ( B ` F )
            +
            ( C ` <. D , G >. )
          )
          ->
          (
            ; 5 5 < ; 8 9
            /\
            ( B ` r ) =
              ( NTP4VCSum C D 0 ( G + 1 ) )
          )
        )
    )
  ) $.
$}

${
  $d i A B C D E F G H I J $.

  ntp4vc-right-loop-definition $a |- (
    NTP4VCRightLoop A B C D E F G H I J
  ) <-> (
    (
      A. i e. NTP4VCBV32
        (
          ( NTP4VCRightInv F D H I J i )
          ->
          ( NTP4VCRightStep A D F H G J i )
        )
    )
    /\
    (
      (
        ; 5 5 < ; 8 9
        /\
        ( D ` J ) = ( NTP4VCSum F H 0 ( I + 1 ) )
      )
      ->
      (
        NTP4VCBestPhase
          A B C D E F G H J
      )
    )
  ) $.
$}

${
  $d o r A B C D E F G H $.

  ntp4vc-fulcrum-definition $a |- (
    NTP4VCFulcrum A B C D E F G H
  ) <-> (
    (
      NTP4VCIn32
        (
          ( G ` H )
          -
          1
        )
    )
    /\
    A. o e. NTP4VCBV32
      (
        o = ( ( G ` H ) - 1 )
        ->
        (
          (
            0 <_ ( o + 1 )
            ->
            (
              (
                ; 5 5 < ; 8 9
                /\
                ( D ` E ) =
                  ( NTP4VCSum F H 0 0 )
              )
              /\
              A. r e. A
                (
                  NTP4VCRightLoop
                    A B C D E F G H o r
                )
            )
          )
          /\
          (
            ( o + 1 ) < 0
            ->
            (
              NTP4VCBestPhase
                A B C D E F G H E
            )
          )
        )
      )
  ) $.
$}

${
  $d a b d e
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Arbitrary source carriers and their total accessors. $)
  ntp4vc-big-zero-member $e |- F e. A $.
  ntp4vc-q-function $e |- C e. ( NTP4VCBV32 ^m A ) $.
  ntp4vc-r-function $e |- D e. ( NTP4VCBV32 ^m A ) $.
  ntp4vc-v-function $e |- E e. ( ZZ ^m A ) $.
  ntp4vc-array-elts-function
    $e |- G e. ( NTP4VCBV32 ^m ( B X. ZZ ) ) $.
  ntp4vc-array-length-function
    $e |- H e. ( NTP4VCBV32 ^m B ) $.

  $( Exact source big-integer invariant, extensionality, and zero laws. $)
  ntp4vc-big-invariant $e |- A. d e. A
    ( NTP4VCBigRep C D E d ) $.
  ntp4vc-big-injective $e |- A. d e. A A. e e. A
    (
      ( NTP4VCCoordEq C D E d e )
      ->
      d = e
    ) $.
  ntp4vc-big-zero-q $e |- ( C ` F ) = 0 $.
  ntp4vc-big-zero-r $e |- ( D ` F ) = 0 $.
  ntp4vc-big-zero-v $e |- ( E ` F ) = 0 $.

  $( Source theorem parameter and fact0. $)
  ntp4vc-array-parameter $e |- a e. B $.
  ntp4vc-fact0 $e |- ( H ` a ) < ( ( 2 ^ ; 3 1 ) - 1 ) $.

  ntp4vc-pearl-hillel-fulcrum-no-overflow-vc $a |- (
    NTP4VCFulcrum A C D E F G H a
  ) $.
$}
