$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/coincidence_count_CoincidenceCountBag_coincidence_countqtvc: the
  coincidence-count verification condition maintains the cardinality of the
  multiset intersection of suffixes of two increasing integer lists while
  advancing their indices according to the compared elements. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source integer-to-natural conversion, and NTP4VCAt is the source totalized
  list lookup with integer default 0.

  NTP4VCOcc counts occurrences of an integer in the half-open suffix beginning
  at the converted integer index. NTP4VCCommon sums the minimum of the two
  suffix occurrence counts over the finite union of the lists' ranges. This
  is exactly the cardinality of the source multiset intersection. In
  particular, the recurrence that characterizes bagofsub on valid bounds
  yields these occurrence counts in both directions.

  NTP4VCStep expands the source Boolean-valued and proposition-valued
  conditionals as pairs of guarded cases. The universally quantified Boolean
  is eliminated by substituting the unique value required by its antecedent:
  it is true exactly when both indices are below their list lengths. This is
  bidirectionally equivalent to the source quantifier and implication.
  Repeated bounds, arithmetic variants, all integer quantifiers, and all
  three comparison branches are retained. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCMin NTP4VCOcc
  NTP4VCCommon NTP4VCIncreasing NTP4VCStep
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-min-syntax $a class ( NTP4VCMin A B ) $.
ntp4vc-occ-syntax $a class ( NTP4VCOcc A B C ) $.
ntp4vc-common-syntax $a class ( NTP4VCCommon A B C D ) $.
ntp4vc-increasing-syntax $a wff ( NTP4VCIncreasing A ) $.
ntp4vc-step-syntax $a wff ( NTP4VCStep A B C D E ) $.

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

ntp4vc-min-definition $a |- (
  NTP4VCMin A B
) = if ( A <_ B , A , B ) $.

${
  $d k A B C $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B C
  ) = (
    # `
    {
      k e. ( ( NTP4VCToNat B ) ..^ ( # ` A ) )
      |
      ( A ` k ) = C
    }
  ) $.
$}

${
  $d v A B C D $.

  ntp4vc-common-definition $a |- (
    NTP4VCCommon A B C D
  ) = (
    sum_ v e. ( ( ran A ) u. ( ran C ) )
      (
        NTP4VCMin
          ( NTP4VCOcc A B v )
          ( NTP4VCOcc C D v )
      )
  ) $.
$}

${
  $d i j A $.

  ntp4vc-increasing-definition $a |- (
    NTP4VCIncreasing A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ZZ
      A. j e. ZZ
        (
          (
            0 <_ i
            /\
            (
              i < j
              /\
              j < ( # ` A )
            )
          )
          ->
          ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
        )
  ) $.
$}

${
  $d A B C D E $.

  $( Source arguments: A=a, B=b, C=c, D=j, and E=i. $)

  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C D E
  ) <-> (
    (
      (
        E < ( # ` A )
        /\
        D < ( # ` B )
      )
      ->
      (
        (
          0 <_ D
          /\
          D < ( # ` B )
        )
        /\
        (
          (
            0 <_ E
            /\
            E < ( # ` A )
          )
          /\
          (
            (
              ( NTP4VCAt A E ) < ( NTP4VCAt B D )
              ->
              (
                (
                  0 <_
                    (
                      (
                        ( # ` A ) - E
                      )
                      +
                      (
                        ( # ` B ) - D
                      )
                    )
                  /\
                  (
                    (
                      (
                        ( # ` A ) - ( E + 1 )
                      )
                      +
                      (
                        ( # ` B ) - D
                      )
                    )
                    <
                    (
                      (
                        ( # ` A ) - E
                      )
                      +
                      (
                        ( # ` B ) - D
                      )
                    )
                  )
                )
                /\
                (
                  (
                    0 <_ ( E + 1 )
                    /\
                    ( E + 1 ) <_ ( # ` A )
                  )
                  /\
                  (
                    (
                      0 <_ D
                      /\
                      D <_ ( # ` B )
                    )
                    /\
                    (
                      C
                      +
                      ( NTP4VCCommon A ( E + 1 ) B D )
                    )
                    =
                    ( NTP4VCCommon A 0 B 0 )
                  )
                )
              )
            )
            /\
            (
              -. ( NTP4VCAt A E ) < ( NTP4VCAt B D )
              ->
              (
                (
                  0 <_ D
                  /\
                  D < ( # ` B )
                )
                /\
                (
                  (
                    0 <_ E
                    /\
                    E < ( # ` A )
                  )
                  /\
                  (
                    (
                      ( NTP4VCAt B D ) < ( NTP4VCAt A E )
                      ->
                      (
                        (
                          0 <_
                            (
                              (
                                ( # ` A ) - E
                              )
                              +
                              (
                                ( # ` B ) - D
                              )
                            )
                          /\
                          (
                            (
                              (
                                ( # ` A ) - E
                              )
                              +
                              (
                                ( # ` B ) - ( D + 1 )
                              )
                            )
                            <
                            (
                              (
                                ( # ` A ) - E
                              )
                              +
                              (
                                ( # ` B ) - D
                              )
                            )
                          )
                        )
                        /\
                        (
                          (
                            0 <_ E
                            /\
                            E <_ ( # ` A )
                          )
                          /\
                          (
                            (
                              0 <_ ( D + 1 )
                              /\
                              ( D + 1 ) <_ ( # ` B )
                            )
                            /\
                            (
                              C
                              +
                              ( NTP4VCCommon A E B ( D + 1 ) )
                            )
                            =
                            ( NTP4VCCommon A 0 B 0 )
                          )
                        )
                      )
                    )
                    /\
                    (
                      -. ( NTP4VCAt B D ) < ( NTP4VCAt A E )
                      ->
                      (
                        (
                          0 <_
                            (
                              (
                                ( # ` A ) - E
                              )
                              +
                              (
                                ( # ` B ) - D
                              )
                            )
                          /\
                          (
                            (
                              (
                                ( # ` A ) - ( E + 1 )
                              )
                              +
                              (
                                ( # ` B ) - ( D + 1 )
                              )
                            )
                            <
                            (
                              (
                                ( # ` A ) - E
                              )
                              +
                              (
                                ( # ` B ) - D
                              )
                            )
                          )
                        )
                        /\
                        (
                          (
                            0 <_ ( E + 1 )
                            /\
                            ( E + 1 ) <_ ( # ` A )
                          )
                          /\
                          (
                            (
                              0 <_ ( D + 1 )
                              /\
                              ( D + 1 ) <_ ( # ` B )
                            )
                            /\
                            (
                              (
                                C + 1
                              )
                              +
                              (
                                NTP4VCCommon
                                  A ( E + 1 ) B ( D + 1 )
                              )
                            )
                            =
                            ( NTP4VCCommon A 0 B 0 )
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
    )
    /\
    (
      -.
      (
        E < ( # ` A )
        /\
        D < ( # ` B )
      )
      ->
      C = ( NTP4VCCommon A 0 B 0 )
    )
  ) $.
$}

${
  $d c i j A B $.

  $( Source parameters: A=a and B=b. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-b-list $e |- B e. Word ZZ $.
  ntp4vc-a-increasing $e |- ( NTP4VCIncreasing A ) $.
  ntp4vc-b-increasing $e |- ( NTP4VCIncreasing B ) $.

  ntp4vc-pearl-coincidence-count-vc $a |- (
    0 <_ 0
    /\
    (
      0 <_ ( # ` A )
      /\
      (
        0 <_ 0
        /\
        (
          0 <_ ( # ` B )
          /\
          (
            (
              0 + ( NTP4VCCommon A 0 B 0 )
            )
            =
            ( NTP4VCCommon A 0 B 0 )
            /\
            A. c e. ZZ
              A. j e. ZZ
                A. i e. ZZ
                  (
                    (
                      (
                        0 <_ i
                        /\
                        i <_ ( # ` A )
                      )
                      /\
                      (
                        (
                          0 <_ j
                          /\
                          j <_ ( # ` B )
                        )
                        /\
                        (
                          c + ( NTP4VCCommon A i B j )
                        )
                        =
                        ( NTP4VCCommon A 0 B 0 )
                      )
                    )
                    ->
                    ( NTP4VCStep A B c j i )
                  )
          )
        )
      )
    )
  ) $.
$}
