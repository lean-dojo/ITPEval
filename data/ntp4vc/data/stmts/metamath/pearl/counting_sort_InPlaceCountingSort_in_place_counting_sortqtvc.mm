$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/counting_sort_InPlaceCountingSort_in_place_counting_sortqtvc: the
  in-place counting-sort verification condition states the counting and
  writing loop invariants, list-update obligations, and the final sorted
  permutation result for an integer list whose values lie below a positive
  bound. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat and
  NTP4VCAt are the source integer-to-natural conversion and totalized list
  lookup with integer default 0. NTP4VCSet is the exact source List.set
  operation after integer-to-natural conversion.

  NTP4VCNumEq and NTP4VCNumLt are the cardinalities of the appropriate
  half-open integer-index sets, exactly expanding the source numof-based
  definitions. NTP4VCSortedSub, NTP4VCSorted, NTP4VCKValues, and
  NTP4VCPermut directly encode the imported source predicates. The remaining
  named predicates only factor the nested counting and writing invariants;
  expanding them recovers every source quantifier, implication, conjunction,
  bound, arithmetic expression, and both conditional branches.

  The positive integer bound is the source global k together with k'def.
  Every integer and integer-list quantifier retains its full source domain.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet
  NTP4VCNumEq NTP4VCNumLt
  NTP4VCZeros NTP4VCKValues
  NTP4VCSortedSub NTP4VCSorted NTP4VCPermut
  NTP4VCCountInv NTP4VCCountStep
  NTP4VCInitial NTP4VCValueInv NTP4VCWriteInv
  NTP4VCAfterWrite NTP4VCNextValue NTP4VCWritePhase
  NTP4VCValueBody NTP4VCValuePhase
  NTP4VCFinish NTP4VCCountPhase
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-numeq-syntax $a class ( NTP4VCNumEq A B C D ) $.
ntp4vc-numlt-syntax $a class ( NTP4VCNumLt A B C D ) $.

ntp4vc-zeros-syntax $a wff ( NTP4VCZeros A B ) $.
ntp4vc-k-values-syntax $a wff ( NTP4VCKValues A B ) $.
ntp4vc-sorted-sub-syntax $a wff ( NTP4VCSortedSub A B C ) $.
ntp4vc-sorted-syntax $a wff ( NTP4VCSorted A ) $.
ntp4vc-permut-syntax $a wff ( NTP4VCPermut A B C ) $.

ntp4vc-count-inv-syntax
  $a wff ( NTP4VCCountInv A B C D ) $.
ntp4vc-count-step-syntax
  $a wff ( NTP4VCCountStep A B C D ) $.
ntp4vc-initial-syntax $a wff ( NTP4VCInitial A ) $.
ntp4vc-value-inv-syntax
  $a wff ( NTP4VCValueInv A B C D ) $.
ntp4vc-write-inv-syntax
  $a wff ( NTP4VCWriteInv A B C D E ) $.
ntp4vc-after-write-syntax
  $a wff ( NTP4VCAfterWrite A B C D E ) $.
ntp4vc-next-value-syntax
  $a wff ( NTP4VCNextValue A B C D ) $.
ntp4vc-write-phase-syntax
  $a wff ( NTP4VCWritePhase A B C D E ) $.
ntp4vc-value-body-syntax
  $a wff ( NTP4VCValueBody A B C D E ) $.
ntp4vc-value-phase-syntax
  $a wff ( NTP4VCValuePhase A B C D E ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C ) $.
ntp4vc-count-phase-syntax
  $a wff ( NTP4VCCountPhase A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

${
  $d n A B C D $.

  ntp4vc-numeq-definition $a |- (
    NTP4VCNumEq A B C D
  ) = (
    # `
    { n e. ( C ..^ D ) | ( NTP4VCAt A n ) = B }
  ) $.
$}

${
  $d n A B C D $.

  ntp4vc-numlt-definition $a |- (
    NTP4VCNumLt A B C D
  ) = (
    # `
    { n e. ( C ..^ D ) | ( NTP4VCAt A n ) < B }
  ) $.
$}

${
  $d i A B $.

  ntp4vc-zeros-definition $a |- (
    NTP4VCZeros A B
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAt A i ) = 0
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-k-values-definition $a |- (
    NTP4VCKValues A B
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        (
          0 <_ ( NTP4VCAt A i )
          /\
          ( NTP4VCAt A i ) < B
        )
      )
  ) $.
$}

${
  $d i j A B C $.

  ntp4vc-sorted-sub-definition $a |- (
    NTP4VCSortedSub A B C
  ) <-> (
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            B <_ i
            /\
            (
              i <_ j
              /\
              j < C
            )
          )
          ->
          ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
        )
  ) $.
$}

ntp4vc-sorted-definition $a |- (
  NTP4VCSorted A
) <-> (
  NTP4VCSortedSub A 0 ( # ` A )
) $.

${
  $d v A B C $.

  ntp4vc-permut-definition $a |- (
    NTP4VCPermut A B C
  ) <-> (
    ( # ` A ) = ( # ` B )
    /\
    A. v e. ZZ
      (
        (
          0 <_ v
          /\
          v < C
        )
        ->
        (
          NTP4VCNumEq A v 0 ( # ` A )
        )
        =
        (
          NTP4VCNumEq B v 0 ( # ` B )
        )
      )
  ) $.
$}

${
  $d v A B C D $.

  ntp4vc-count-inv-definition $a |- (
    NTP4VCCountInv A B C D
  ) <-> (
    A. v e. ZZ
      (
        (
          0 <_ v
          /\
          v < D
        )
        ->
        (
          ( NTP4VCAt B v )
          =
          ( NTP4VCNumEq A v 0 C )
        )
      )
  ) $.
$}

ntp4vc-count-step-definition $a |- (
  NTP4VCCountStep A B C D
) <-> (
  (
    0 <_ C
    /\
    C < ( # ` A )
  )
  /\
  (
    (
      0 <_ ( NTP4VCAt A C )
      /\
      ( NTP4VCAt A C ) < ( # ` B )
    )
    /\
    (
      (
        0 <_ ( NTP4VCAt A C )
        /\
        ( NTP4VCAt A C ) < ( # ` B )
      )
      /\
      (
        (
          # `
          (
            NTP4VCSet
              B
              ( NTP4VCAt A C )
              (
                ( NTP4VCAt B ( NTP4VCAt A C ) )
                +
                1
              )
          )
        )
        =
        ( # ` B )
        ->
        (
          NTP4VCCountInv
            A
            (
              NTP4VCSet
                B
                ( NTP4VCAt A C )
                (
                ( NTP4VCAt B ( NTP4VCAt A C ) )
                +
                1
              )
            )
            ( C + 1 )
            D
        )
      )
    )
  )
) $.

${
  $d p q A $.

  ntp4vc-initial-definition $a |- (
    NTP4VCInitial A
  ) <-> (
    0 = ( NTP4VCNumLt A 0 0 ( # ` A ) )
    /\
    (
      ( NTP4VCSortedSub A 0 0 )
      /\
      (
        A. p e. ZZ
          (
            (
              0 <_ p
              /\
              p < 0
            )
            ->
            (
              0 <_ ( NTP4VCAt A p )
              /\
              ( NTP4VCAt A p ) < 0
            )
          )
        /\
        A. q e. ZZ
          (
            (
              0 <_ q
              /\
              q < 0
            )
            ->
            (
              ( NTP4VCNumEq A q 0 0 )
              =
              ( NTP4VCNumEq A q 0 ( # ` A ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d p q A B C D $.

  ntp4vc-value-inv-definition $a |- (
    NTP4VCValueInv A B C D
  ) <-> (
    C = ( NTP4VCNumLt A D 0 ( # ` B ) )
    /\
    (
      ( NTP4VCSortedSub B 0 C )
      /\
      (
        A. p e. ZZ
          (
            (
              0 <_ p
              /\
              p < C
            )
            ->
            (
              0 <_ ( NTP4VCAt B p )
              /\
              ( NTP4VCAt B p ) < D
            )
          )
        /\
        A. q e. ZZ
          (
            (
              0 <_ q
              /\
              q < D
            )
            ->
            (
              ( NTP4VCNumEq B q 0 C )
              =
              ( NTP4VCNumEq A q 0 ( # ` B ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d p q A B C D E $.

  ntp4vc-write-inv-definition $a |- (
    NTP4VCWriteInv A B C D E
  ) <-> (
    (
      ( ( C - E ) + 1 )
      =
      ( NTP4VCNumLt A D 0 ( # ` B ) )
    )
    /\
    (
      ( NTP4VCSortedSub B 0 C )
      /\
      (
        A. p e. ZZ
          (
            (
              0 <_ p
              /\
              p < C
            )
            ->
            (
              0 <_ ( NTP4VCAt B p )
              /\
              ( NTP4VCAt B p ) <_ D
            )
          )
        /\
        (
          A. q e. ZZ
            (
              (
                0 <_ q
                /\
                q < D
              )
              ->
              (
                ( NTP4VCNumEq B q 0 C )
                =
                ( NTP4VCNumEq A q 0 ( # ` B ) )
              )
            )
          /\
          (
            ( NTP4VCNumEq B D 0 C )
            =
            ( E - 1 )
          )
        )
      )
    )
  ) $.
$}

${
  $d p q A B C D E $.

  ntp4vc-after-write-definition $a |- (
    NTP4VCAfterWrite A B C D E
  ) <-> (
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    /\
    (
      (
        ( # ` ( NTP4VCSet B C D ) )
        =
        ( # ` B )
      )
      ->
      (
        (
          ( ( ( C + 1 ) - ( E + 1 ) ) + 1 )
          =
          (
            NTP4VCNumLt
              A
              D
              0
              ( # ` ( NTP4VCSet B C D ) )
          )
        )
        /\
        (
          (
            NTP4VCSortedSub
              ( NTP4VCSet B C D )
              0
              ( C + 1 )
          )
          /\
          (
            A. p e. ZZ
              (
                (
                  0 <_ p
                  /\
                  p < ( C + 1 )
                )
                ->
                (
                  0 <_
                    (
                      NTP4VCAt
                        ( NTP4VCSet B C D )
                        p
                    )
                  /\
                  (
                    NTP4VCAt
                      ( NTP4VCSet B C D )
                      p
                  )
                  <_
                  D
                )
              )
            /\
            (
              A. q e. ZZ
                (
                  (
                    0 <_ q
                    /\
                    q < D
                  )
                  ->
                  (
                    (
                      NTP4VCNumEq
                        ( NTP4VCSet B C D )
                        q
                        0
                        ( C + 1 )
                    )
                    =
                    (
                      NTP4VCNumEq
                        A
                        q
                        0
                        ( # ` ( NTP4VCSet B C D ) )
                    )
                  )
                )
              /\
              (
                (
                  NTP4VCNumEq
                    ( NTP4VCSet B C D )
                    D
                    0
                    ( C + 1 )
                )
                =
                ( ( E + 1 ) - 1 )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d p q A B C D $.

  ntp4vc-next-value-definition $a |- (
    NTP4VCNextValue A B C D
  ) <-> (
    C = ( NTP4VCNumLt A ( D + 1 ) 0 ( # ` B ) )
    /\
    (
      ( NTP4VCSortedSub B 0 C )
      /\
      (
        A. p e. ZZ
          (
            (
              0 <_ p
              /\
              p < C
            )
            ->
            (
              0 <_ ( NTP4VCAt B p )
              /\
              ( NTP4VCAt B p ) < ( D + 1 )
            )
          )
        /\
        A. q e. ZZ
          (
            (
              0 <_ q
              /\
              q < ( D + 1 )
            )
            ->
            (
              ( NTP4VCNumEq B q 0 C )
              =
              ( NTP4VCNumEq A q 0 ( # ` B ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d i l p q x A B C D E $.

  ntp4vc-write-phase-definition $a |- (
    NTP4VCWritePhase A B C D E
  ) <-> (
    (
      1 <_ ( E + 1 )
      ->
      (
        (
          ( ( C - 1 ) + 1 )
          =
          ( NTP4VCNumLt A D 0 ( # ` B ) )
        )
        /\
        (
          ( NTP4VCSortedSub B 0 C )
          /\
          (
            A. p e. ZZ
              (
                (
                  0 <_ p
                  /\
                  p < C
                )
                ->
                (
                  0 <_ ( NTP4VCAt B p )
                  /\
                  ( NTP4VCAt B p ) <_ D
                )
              )
            /\
            (
              A. q e. ZZ
                (
                  (
                    0 <_ q
                    /\
                    q < D
                  )
                  ->
                  (
                    ( NTP4VCNumEq B q 0 C )
                    =
                    ( NTP4VCNumEq A q 0 ( # ` B ) )
                  )
                )
              /\
              (
                (
                  ( NTP4VCNumEq B D 0 C )
                  =
                  ( 1 - 1 )
                )
                /\
                A. l e. ZZ
                  A. x e. Word ZZ
                    (
                      ( # ` x ) = ( # ` B )
                      ->
                      (
                        A. i e. ZZ
                          (
                            (
                              (
                                1 <_ i
                                /\
                                i <_ E
                              )
                              /\
                              ( NTP4VCWriteInv A x l D i )
                            )
                            ->
                            ( NTP4VCAfterWrite A x l D i )
                          )
                        /\
                        (
                          (
                            NTP4VCWriteInv
                              A
                              x
                              l
                              D
                              ( E + 1 )
                          )
                          ->
                          ( NTP4VCNextValue A x l D )
                        )
                      )
                    )
              )
            )
          )
        )
      )
    )
    /\
    (
      ( E + 1 ) < 1
      ->
      ( NTP4VCNextValue A B C D )
    )
  ) $.
$}

ntp4vc-value-body-definition $a |- (
  NTP4VCValueBody A B C D E
) <-> (
  (
    0 <_ E
    /\
    E < ( # ` B )
  )
  /\
  (
    NTP4VCWritePhase
      A
      C
      D
      E
      ( NTP4VCAt B E )
  )
) $.

${
  $d v A B C D E $.

  ntp4vc-value-phase-definition $a |- (
    NTP4VCValuePhase A B C D E
  ) <-> (
    A. v e. ZZ
      (
        (
          (
            0 <_ v
            /\
            v <_ ( E - 1 )
          )
          /\
          ( NTP4VCValueInv A C D v )
        )
        ->
        ( NTP4VCValueBody A B C D v )
      )
    /\
    (
      (
        NTP4VCValueInv
          A
          C
          D
          ( ( E - 1 ) + 1 )
      )
      ->
      (
        ( NTP4VCSorted C )
        /\
        ( NTP4VCPermut A C E )
      )
    )
  ) $.
$}

${
  $d j x A B C $.

  ntp4vc-finish-definition $a |- (
    NTP4VCFinish A B C
  ) <-> (
    (
      0 <_ ( ( C - 1 ) + 1 )
      ->
      (
        ( NTP4VCInitial A )
        /\
        A. j e. ZZ
          A. x e. Word ZZ
            (
              ( # ` x ) = ( # ` A )
              ->
              ( NTP4VCValuePhase A B x j C )
            )
      )
    )
    /\
    (
      ( ( C - 1 ) + 1 ) < 0
      ->
      (
        ( NTP4VCSorted A )
        /\
        ( NTP4VCPermut A A C )
      )
    )
  ) $.
$}

${
  $d i x A B C $.

  ntp4vc-count-phase-definition $a |- (
    NTP4VCCountPhase A B C
  ) <-> (
    ( NTP4VCCountInv A B 0 C )
    /\
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          A. i e. ZZ
            (
              (
                (
                  0 <_ i
                  /\
                  i <_ ( ( # ` A ) - 1 )
                )
                /\
                ( NTP4VCCountInv A x i C )
              )
              ->
              ( NTP4VCCountStep A x i C )
            )
          /\
          (
            (
              NTP4VCCountInv
                A
                x
                ( ( ( # ` A ) - 1 ) + 1 )
                C
            )
            ->
            ( NTP4VCFinish A x C )
          )
        )
      )
  ) $.
$}

${
  $d x A B $.

  $( Source theorem parameters: A=a and B=k. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-k-int $e |- B e. ZZ $.
  ntp4vc-k-positive $e |- 0 < B $.
  ntp4vc-a-k-values $e |- ( NTP4VCKValues A B ) $.

  ntp4vc-pearl-in-place-counting-sort-vc $a |- (
    0 <_ B
    /\
    A. x e. Word ZZ
      (
        (
          ( NTP4VCZeros x B )
          /\
          ( # ` x ) = B
        )
        ->
        (
          (
            0 <_ ( ( ( # ` A ) - 1 ) + 1 )
            ->
            ( NTP4VCCountPhase A x B )
          )
          /\
          (
            ( ( ( # ` A ) - 1 ) + 1 ) < 0
            ->
            ( NTP4VCFinish A x B )
          )
        )
      )
  ) $.
$}
