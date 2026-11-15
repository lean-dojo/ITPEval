$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc:
  the Colored Tiles enumeration verification condition initializes the
  finite sets of valid red/black rows, preserves their cardinalities through
  the nested first-black-tile loop, and establishes the enumeration result
  for every length from zero through fifty. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Colors are exactly SetMM's two-element carrier 2, with Black = 0 and
  Red = 1. Word 2 is the full source type of finite colorings, ZZ is the
  unbounded integer domain, and NTP4VCColoringSet is exactly the carrier of
  finite sets of colorings. Finite Why3 arrays are represented by words.
  NTP4VCUpdateLaw compares an updated word with its predecessor exactly on
  the source array domain 0 <= i < length. On this guarded domain the
  integer-to-natural index conversion is injective and the word encoding is
  bidirectionally equivalent to integer-keyed Why3 array update semantics;
  negative-index aliases introduced by the secondary list exports are not
  part of the source array domain.

  D is the source's arbitrary inhabited default color. F and G are,
  respectively, first_black_tile and addleft. Their displayed hypotheses
  retain the complete source recursion and contracts. NTP4VCValid,
  NTP4VCMapAddLeft, the loop invariants, update laws, disjoint unions, and
  final postcondition are explicit bidirectional definitions.

  Definitional abbreviations factor the generated verification condition
  without deleting its initialization bounds, list-update implications,
  nested-loop state quantifiers, cardinality premises, or fallback branches.
  The final $a declaration is Metamath's native unproved statement encoding;
  every preceding $a declaration is syntax or a faithful definition, and
  this database contains no $p proof declaration.
$)

$c
  NTP4VCColoringSet
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCTail NTP4VCRepeat
  NTP4VCO1 NTP4VCO2 NTP4VCO3 NTP4VCO4
  NTP4VCCount0 NTP4VCCount1 NTP4VCCount2 NTP4VCCount3
  NTP4VCSets0 NTP4VCSets1 NTP4VCSets2 NTP4VCSets3
  NTP4VCMapAddLeft
  NTP4VCTwoRedNeighbors NTP4VCValid NTP4VCUpdateLaw
  NTP4VCBaseInv NTP4VCInnerInv NTP4VCFinalPost
  NTP4VCInnerBody NTP4VCAddRed NTP4VCInnerLoop
  NTP4VCOuterBody NTP4VCRun NTP4VCInitVC NTP4VCEnumVC
$.

ntp4vc-coloring-set-syntax $a class NTP4VCColoringSet $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-tail-syntax $a class ( NTP4VCTail A ) $.
ntp4vc-repeat-syntax $a class ( NTP4VCRepeat A B ) $.
ntp4vc-o1-syntax $a class NTP4VCO1 $.
ntp4vc-o2-syntax $a class NTP4VCO2 $.
ntp4vc-o3-syntax $a class NTP4VCO3 $.
ntp4vc-o4-syntax $a class NTP4VCO4 $.
ntp4vc-count0-syntax $a class ( NTP4VCCount0 A ) $.
ntp4vc-count1-syntax $a class ( NTP4VCCount1 A ) $.
ntp4vc-count2-syntax $a class ( NTP4VCCount2 A ) $.
ntp4vc-count3-syntax $a class ( NTP4VCCount3 A ) $.
ntp4vc-sets0-syntax $a class ( NTP4VCSets0 A ) $.
ntp4vc-sets1-syntax $a class ( NTP4VCSets1 A ) $.
ntp4vc-sets2-syntax $a class ( NTP4VCSets2 A ) $.
ntp4vc-sets3-syntax $a class ( NTP4VCSets3 A ) $.
ntp4vc-map-add-left-syntax
  $a class ( NTP4VCMapAddLeft A B C ) $.

ntp4vc-two-red-neighbors-syntax
  $a wff ( NTP4VCTwoRedNeighbors A B C ) $.
ntp4vc-valid-syntax
  $a wff ( NTP4VCValid A B ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C D E ) $.
ntp4vc-base-inv-syntax
  $a wff ( NTP4VCBaseInv A B C D ) $.
ntp4vc-inner-inv-syntax
  $a wff ( NTP4VCInnerInv A B C D E F ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C ) $.
ntp4vc-inner-body-syntax
  $a wff ( NTP4VCInnerBody A B C D E F G ) $.
ntp4vc-add-red-syntax
  $a wff ( NTP4VCAddRed A B C D ) $.
ntp4vc-inner-loop-syntax
  $a wff ( NTP4VCInnerLoop A B C D E F G ) $.
ntp4vc-outer-body-syntax
  $a wff ( NTP4VCOuterBody A B C D E F ) $.
ntp4vc-run-syntax
  $a wff ( NTP4VCRun A B C D E ) $.
ntp4vc-init-vc-syntax
  $a wff ( NTP4VCInitVC A B C D E ) $.
ntp4vc-enum-vc-syntax
  $a wff ( NTP4VCEnumVC A B C ) $.

${
  $d s A $.

  ntp4vc-coloring-set-definition $a |- NTP4VCColoringSet = {
    s e. Fin | s C_ ( Word 2 )
  } $.
$}

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat C ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat C ) ) ,
  B
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
  $d k A $.

  ntp4vc-tail-definition $a |- (
    NTP4VCTail A
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) - 1 ) ) |->
      ( A ` ( k + 1 ) )
  ) $.
$}

${
  $d k A B $.

  ntp4vc-repeat-definition $a |- (
    NTP4VCRepeat A B
  ) = (
    k e. ( 0 ..^ ( NTP4VCToNat A ) ) |-> B
  ) $.
$}

ntp4vc-o1-definition $a |- NTP4VCO1 = { (/) } $.
ntp4vc-o2-definition $a |- NTP4VCO2 = { <" 0 "> } $.
ntp4vc-o3-definition $a |- NTP4VCO3 = {
  ( <" 0 "> ++ <" 0 "> )
} $.
ntp4vc-o4-definition $a |- NTP4VCO4 = {
  ( ( <" 1 "> ++ <" 1 "> ) ++ <" 1 "> ) ,
  ( ( <" 0 "> ++ <" 0 "> ) ++ <" 0 "> )
} $.

ntp4vc-count0-definition $a |- (
  NTP4VCCount0 A
) = ( NTP4VCSet A 0 1 ) $.
ntp4vc-count1-definition $a |- (
  NTP4VCCount1 A
) = ( NTP4VCSet ( NTP4VCCount0 A ) 1 1 ) $.
ntp4vc-count2-definition $a |- (
  NTP4VCCount2 A
) = ( NTP4VCSet ( NTP4VCCount1 A ) 2 1 ) $.
ntp4vc-count3-definition $a |- (
  NTP4VCCount3 A
) = ( NTP4VCSet ( NTP4VCCount2 A ) 3 2 ) $.

ntp4vc-sets0-definition $a |- (
  NTP4VCSets0 A
) = ( NTP4VCSet A 0 NTP4VCO1 ) $.
ntp4vc-sets1-definition $a |- (
  NTP4VCSets1 A
) = ( NTP4VCSet ( NTP4VCSets0 A ) 1 NTP4VCO2 ) $.
ntp4vc-sets2-definition $a |- (
  NTP4VCSets2 A
) = ( NTP4VCSet ( NTP4VCSets1 A ) 2 NTP4VCO3 ) $.
ntp4vc-sets3-definition $a |- (
  NTP4VCSets3 A
) = ( NTP4VCSet ( NTP4VCSets2 A ) 3 NTP4VCO4 ) $.

${
  $d x y A B C $.

  ntp4vc-map-add-left-definition $a |- (
    NTP4VCMapAddLeft A B C
  ) = {
    y e. ( Word 2 ) |
      E. x e. A
        y = ( C ` <. B , x >. )
  } $.
$}

ntp4vc-two-red-neighbors-definition $a |- (
  NTP4VCTwoRedNeighbors A B C
) <-> (
  (
    ( NTP4VCAt A C ( B - 2 ) ) = 1
    /\
    (
      ( NTP4VCAt A C ( B - 1 ) ) = 1
      /\
      2 <_ B
    )
  )
  \/
  (
    (
      ( NTP4VCAt A C ( B - 1 ) ) = 1
      /\
      ( NTP4VCAt A C ( B + 1 ) ) = 1
    )
    /\
    (
      1 <_ B
      /\
      B <_ ( ( # ` A ) - 2 )
    )
  )
  \/
  (
    ( NTP4VCAt A C ( B + 1 ) ) = 1
    /\
    (
      ( NTP4VCAt A C ( B + 2 ) ) = 1
      /\
      B <_ ( ( # ` A ) - 3 )
    )
  )
) $.

${
  $d i A B $.

  ntp4vc-valid-definition $a |- (
    NTP4VCValid A B
  ) <-> A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < ( # ` A )
      )
      ->
      (
        ( NTP4VCAt A B i ) = 1
        ->
        ( NTP4VCTwoRedNeighbors A i B )
      )
    ) $.
$}

${
  $d i A B C D E $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C D E
  ) <-> A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < ( # ` B )
      )
      ->
      (
        ( NTP4VCAt A C i )
        =
        if (
          i = D ,
          E ,
          ( NTP4VCAt B C i )
        )
      )
    ) $.
$}

${
  $d c i A B C D $.

  ntp4vc-base-inv-definition $a |- (
    NTP4VCBaseInv A B C D
  ) <-> (
    (
      A. c e. ( Word 2 )
        (
          (
            0 <_ ( # ` c )
            /\
            ( # ` c ) < C
          )
          ->
          (
            ( NTP4VCValid c D )
            ->
            c e. ( NTP4VCAt A (/) ( # ` c ) )
          )
        )
    )
    /\
    (
      A. c e. ( Word 2 ) A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < C
          )
          ->
          (
            c e. ( NTP4VCAt A (/) i )
            ->
            (
              ( # ` c ) = i
              /\
              ( NTP4VCValid c D )
            )
          )
        )
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        ( NTP4VCAt B 0 i )
        =
        ( # ` ( NTP4VCAt A (/) i ) )
      )
  ) $.
$}

${
  $d c A B C D E F $.

  ntp4vc-inner-inv-definition $a |- (
    NTP4VCInnerInv A B C D E F
  ) <-> (
    ( NTP4VCBaseInv A B C F )
    /\
    (
      A. c e. ( Word 2 )
        (
          c e. ( NTP4VCAt A (/) C )
          <->
          (
            ( # ` c ) = C
            /\
            (
              ( NTP4VCValid c F )
              /\
              ( E ` c ) < D
            )
          )
        )
    )
    /\
    ( NTP4VCAt B 0 C )
    =
    ( # ` ( NTP4VCAt A (/) C ) )
  ) $.
$}

${
  $d c i A B C $.

  ntp4vc-final-post-definition $a |- (
    NTP4VCFinalPost A B C
  ) <-> (
    (
      ( # ` B ) = ; 5 1
      /\
      ; 5 1 = ( # ` A )
    )
    /\
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i <_ ; 5 0
          )
          ->
          A. c e. ( Word 2 )
            (
              ( # ` c ) = i
              ->
              (
                ( NTP4VCValid c C )
                <->
                c e. ( NTP4VCAt A (/) i )
              )
            )
        )
    )
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ; 5 0
        )
        ->
        ( NTP4VCAt B 0 i )
        =
        ( # ` ( NTP4VCAt A (/) i ) )
      )
  ) $.
$}

${
  $d c i x A B C D E F G $.

  $( A=sets2, B=count2, C=n, D=k, E=first_black_tile,
     F=default color, and G=addleft. $)
  ntp4vc-inner-body-definition $a |- (
    NTP4VCInnerBody A B C D E F G
  ) <-> (
    (
      0 <_ ( C - D - 1 )
      /\
      ( C - D - 1 ) < ( # ` B )
    )
    /\
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    /\
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    /\
    (
      ( # ` (
        NTP4VCSet
          B
          C
          (
            ( NTP4VCAt B 0 C )
            +
            ( NTP4VCAt B 0 ( C - D - 1 ) )
          )
      ) ) = ( # ` B )
      ->
      (
        (
          NTP4VCUpdateLaw
            (
              NTP4VCSet
                B
                C
                (
                  ( NTP4VCAt B 0 C )
                  +
                  ( NTP4VCAt B 0 ( C - D - 1 ) )
                )
            )
            B
            0
            C
            (
              ( NTP4VCAt B 0 C )
              +
              ( NTP4VCAt B 0 ( C - D - 1 ) )
            )
        )
        ->
        (
          (
            0 <_ ( C - D - 1 )
            /\
            ( C - D - 1 ) < ( # ` A )
          )
          /\
          (
            0 <_ C
            /\
            C < ( # ` A )
          )
          /\
          (
            A. x e. ( Word 2 )
              (
                x e. ( NTP4VCAt A (/) C )
                ->
                -. x e. (
                  NTP4VCMapAddLeft
                    ( NTP4VCAt A (/) ( C - D - 1 ) )
                    D
                    G
                )
              )
          )
          /\
          (
            (
              # ` (
                ( NTP4VCAt A (/) C )
                u.
                (
                  NTP4VCMapAddLeft
                    ( NTP4VCAt A (/) ( C - D - 1 ) )
                    D
                    G
                )
              )
            )
            =
            (
              ( # ` ( NTP4VCAt A (/) C ) )
              +
              (
                # ` (
                  NTP4VCMapAddLeft
                    ( NTP4VCAt A (/) ( C - D - 1 ) )
                    D
                    G
                )
              )
            )
            ->
            (
              (
                0 <_ C
                /\
                C < ( # ` A )
              )
              /\
              (
                (
                  # ` (
                    NTP4VCSet
                      A
                      C
                      (
                        ( NTP4VCAt A (/) C )
                        u.
                        (
                          NTP4VCMapAddLeft
                            ( NTP4VCAt A (/) ( C - D - 1 ) )
                            D
                            G
                        )
                      )
                  )
                ) = ( # ` A )
                ->
                (
                  (
                    NTP4VCUpdateLaw
                      (
                        NTP4VCSet
                          A
                          C
                          (
                            ( NTP4VCAt A (/) C )
                            u.
                            (
                              NTP4VCMapAddLeft
                                ( NTP4VCAt A (/) ( C - D - 1 ) )
                                D
                                G
                            )
                          )
                      )
                      A
                      (/)
                      C
                      (
                        ( NTP4VCAt A (/) C )
                        u.
                        (
                          NTP4VCMapAddLeft
                            ( NTP4VCAt A (/) ( C - D - 1 ) )
                            D
                            G
                        )
                      )
                  )
                  ->
                  (
                    NTP4VCInnerInv
                      (
                        NTP4VCSet
                          A
                          C
                          (
                            ( NTP4VCAt A (/) C )
                            u.
                            (
                              NTP4VCMapAddLeft
                                ( NTP4VCAt A (/) ( C - D - 1 ) )
                                D
                                G
                            )
                          )
                      )
                      (
                        NTP4VCSet
                          B
                          C
                          (
                            ( NTP4VCAt B 0 C )
                            +
                            ( NTP4VCAt B 0 ( C - D - 1 ) )
                          )
                      )
                      C
                      ( D + 1 )
                      E
                      F
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
  $d i x A B C D $.

  $( A=sets, B=count, C=n, and D=default color. $)
  ntp4vc-add-red-definition $a |- (
    NTP4VCAddRed A B C D
  ) <-> (
    0 <_ C
    /\
    (
      (
        ( # ` ( NTP4VCRepeat C 1 ) ) = C
        /\
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i < C
            )
            ->
            ( NTP4VCAt ( NTP4VCRepeat C 1 ) D i ) = 1
          )
      )
      ->
      (
        (
          0 <_ C
          /\
          C < ( # ` B )
        )
        /\
        (
          0 <_ C
          /\
          C < ( # ` B )
        )
        /\
        (
          (
            # ` (
              NTP4VCSet
                B
                C
                ( ( NTP4VCAt B 0 C ) + 1 )
            )
          ) = ( # ` B )
          ->
          (
            (
              NTP4VCUpdateLaw
                (
                  NTP4VCSet
                    B
                    C
                    ( ( NTP4VCAt B 0 C ) + 1 )
                )
                B
                0
                C
                ( ( NTP4VCAt B 0 C ) + 1 )
            )
            ->
            (
              (
                0 <_ C
                /\
                C < ( # ` A )
              )
              /\
              (
                A. x e. ( Word 2 )
                  (
                    x e. ( NTP4VCAt A (/) C )
                    ->
                    -. x e. { ( NTP4VCRepeat C 1 ) }
                  )
              )
              /\
              (
                (
                  # ` (
                    ( NTP4VCAt A (/) C )
                    u.
                    { ( NTP4VCRepeat C 1 ) }
                  )
                )
                =
                (
                  ( # ` ( NTP4VCAt A (/) C ) )
                  +
                  ( # ` { ( NTP4VCRepeat C 1 ) } )
                )
                ->
                (
                  (
                    0 <_ C
                    /\
                    C < ( # ` A )
                  )
                  /\
                  (
                    (
                      # ` (
                        NTP4VCSet
                          A
                          C
                          (
                            ( NTP4VCAt A (/) C )
                            u.
                            { ( NTP4VCRepeat C 1 ) }
                          )
                      )
                    ) = ( # ` A )
                    ->
                    (
                      (
                        NTP4VCUpdateLaw
                          (
                            NTP4VCSet
                              A
                              C
                              (
                                ( NTP4VCAt A (/) C )
                                u.
                                { ( NTP4VCRepeat C 1 ) }
                              )
                          )
                          A
                          (/)
                          C
                          (
                            ( NTP4VCAt A (/) C )
                            u.
                            { ( NTP4VCRepeat C 1 ) }
                          )
                      )
                      ->
                      (
                        NTP4VCBaseInv
                          (
                            NTP4VCSet
                              A
                              C
                              (
                                ( NTP4VCAt A (/) C )
                                u.
                                { ( NTP4VCRepeat C 1 ) }
                              )
                          )
                          (
                            NTP4VCSet
                              B
                              C
                              ( ( NTP4VCAt B 0 C ) + 1 )
                          )
                          ( C + 1 )
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
    )
  ) $.
$}

${
  $d k A B C D E F G $.

  $( A=sets after the k=3 seed, B=count after that seed, C=n,
     D=n-1, E=first_black_tile, F=default color, and G=addleft. $)
  ntp4vc-inner-loop-definition $a |- (
    NTP4VCInnerLoop A B C D E F G
  ) <-> A. s e. ( Word NTP4VCColoringSet )
    A. t e. ( Word ZZ )
      (
        ( # ` s ) = ( # ` A )
        ->
        (
          ( # ` t ) = ( # ` B )
          ->
          (
            (
              A. k e. ZZ
                (
                  (
                    (
                      3 <_ k
                      /\
                      k <_ D
                    )
                    /\
                    ( NTP4VCInnerInv s t C k E F )
                  )
                  ->
                  ( NTP4VCInnerBody s t C k E F G )
                )
            )
            /\
            (
              ( NTP4VCInnerInv s t C ( D + 1 ) E F )
              ->
              ( NTP4VCAddRed s t C F )
            )
          )
        )
      ) $.
$}

${
  $d n A B C D E F $.

  $( A=sets1, B=count1, C=n, D=first_black_tile,
     E=default color, and F=addleft. $)
  ntp4vc-outer-body-definition $a |- (
    NTP4VCOuterBody A B C D E F
  ) <-> (
    (
      0 <_ ( C - 1 )
      /\
      ( C - 1 ) < ( # ` B )
    )
    /\
    (
      0 <_ C
      /\
      C < ( # ` B )
    )
    /\
    (
      (
        # ` (
          NTP4VCSet B C ( NTP4VCAt B 0 ( C - 1 ) )
        )
      ) = ( # ` B )
      ->
      (
        (
          NTP4VCUpdateLaw
            (
              NTP4VCSet B C ( NTP4VCAt B 0 ( C - 1 ) )
            )
            B
            0
            C
            ( NTP4VCAt B 0 ( C - 1 ) )
        )
        ->
        (
          (
            0 <_ ( C - 1 )
            /\
            ( C - 1 ) < ( # ` A )
          )
          /\
          (
            0 <_ C
            /\
            C < ( # ` A )
          )
          /\
          (
            (
              # ` (
                NTP4VCSet
                  A
                  C
                  (
                    NTP4VCMapAddLeft
                      ( NTP4VCAt A (/) ( C - 1 ) )
                      0
                      F
                  )
              )
            ) = ( # ` A )
            ->
            (
              (
                NTP4VCUpdateLaw
                  (
                    NTP4VCSet
                      A
                      C
                      (
                        NTP4VCMapAddLeft
                          ( NTP4VCAt A (/) ( C - 1 ) )
                          0
                          F
                      )
                  )
                  A
                  (/)
                  C
                  (
                    NTP4VCMapAddLeft
                      ( NTP4VCAt A (/) ( C - 1 ) )
                      0
                      F
                  )
              )
              ->
              (
                (
                  3 <_ ( ( C - 1 ) + 1 )
                  ->
                  (
                    (
                      NTP4VCInnerInv
                        (
                          NTP4VCSet
                            A
                            C
                            (
                              NTP4VCMapAddLeft
                                ( NTP4VCAt A (/) ( C - 1 ) )
                                0
                                F
                            )
                        )
                        (
                          NTP4VCSet
                            B
                            C
                            ( NTP4VCAt B 0 ( C - 1 ) )
                        )
                        C
                        3
                        D
                        E
                    )
                    /\
                    (
                      NTP4VCInnerLoop
                        (
                          NTP4VCSet
                            A
                            C
                            (
                              NTP4VCMapAddLeft
                                ( NTP4VCAt A (/) ( C - 1 ) )
                                0
                                F
                            )
                        )
                        (
                          NTP4VCSet
                            B
                            C
                            ( NTP4VCAt B 0 ( C - 1 ) )
                        )
                        C
                        ( C - 1 )
                        D
                        E
                        F
                    )
                  )
                )
                /\
                (
                  ( ( C - 1 ) + 1 ) < 3
                  ->
                  (
                    NTP4VCAddRed
                      (
                        NTP4VCSet
                          A
                          C
                          (
                            NTP4VCMapAddLeft
                              ( NTP4VCAt A (/) ( C - 1 ) )
                              0
                              F
                          )
                      )
                      (
                        NTP4VCSet
                          B
                          C
                          ( NTP4VCAt B 0 ( C - 1 ) )
                      )
                      C
                      E
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
  $d n A B C D E $.

  $( A=initialized sets, B=initialized count, C=first_black_tile,
     D=default color, and E=addleft. $)
  ntp4vc-run-definition $a |- (
    NTP4VCRun A B C D E
  ) <-> (
    (
      4 <_ ( ; 5 0 + 1 )
      ->
      (
        ( NTP4VCBaseInv A B 4 D )
        /\
        A. s e. ( Word NTP4VCColoringSet )
          A. t e. ( Word ZZ )
            (
              ( # ` s ) = ( # ` A )
              ->
              (
                ( # ` t ) = ( # ` B )
                ->
                (
                  (
                    A. n e. ZZ
                      (
                        (
                          (
                            4 <_ n
                            /\
                            n <_ ; 5 0
                          )
                          /\
                          ( NTP4VCBaseInv s t n D )
                        )
                        ->
                        ( NTP4VCOuterBody s t n C D E )
                      )
                  )
                  /\
                  (
                    ( NTP4VCBaseInv s t ( ; 5 0 + 1 ) D )
                    ->
                    ( NTP4VCFinalPost s t D )
                  )
                )
              )
            )
      )
    )
    /\
    (
      ( ; 5 0 + 1 ) < 4
      ->
      ( NTP4VCFinalPost A B D )
    )
  ) $.
$}

ntp4vc-init-vc-definition $a |- (
  NTP4VCInitVC A B C D E
) <-> (
  (
    0 <_ 0
    /\
    0 < ( # ` A )
  )
  /\
  (
    ( # ` ( NTP4VCCount0 A ) ) = ( # ` A )
    ->
    (
      ( NTP4VCUpdateLaw ( NTP4VCCount0 A ) A 0 0 1 )
      ->
      (
        (
          0 <_ 0
          /\
          0 < ( # ` B )
        )
        /\
        (
          ( # ` ( NTP4VCSets0 B ) ) = ( # ` B )
          ->
          (
            (
              NTP4VCUpdateLaw
                ( NTP4VCSets0 B ) B (/) 0 NTP4VCO1
            )
            ->
            (
              (
                0 <_ 1
                /\
                1 < ( # ` ( NTP4VCCount0 A ) )
              )
              /\
              (
                (
                  # ` ( NTP4VCCount1 A )
                ) = ( # ` ( NTP4VCCount0 A ) )
                ->
                (
                  (
                    NTP4VCUpdateLaw
                      ( NTP4VCCount1 A )
                      ( NTP4VCCount0 A )
                      0
                      1
                      1
                  )
                  ->
                  (
                    (
                      0 <_ 1
                      /\
                      1 < ( # ` ( NTP4VCSets0 B ) )
                    )
                    /\
                    (
                      (
                        # ` ( NTP4VCSets1 B )
                      ) = ( # ` ( NTP4VCSets0 B ) )
                      ->
                      (
                        (
                          NTP4VCUpdateLaw
                            ( NTP4VCSets1 B )
                            ( NTP4VCSets0 B )
                            (/)
                            1
                            NTP4VCO2
                        )
                        ->
                        (
                          (
                            0 <_ 2
                            /\
                            2 < ( # ` ( NTP4VCCount1 A ) )
                          )
                          /\
                          (
                            (
                              # ` ( NTP4VCCount2 A )
                            ) = ( # ` ( NTP4VCCount1 A ) )
                            ->
                            (
                              (
                                NTP4VCUpdateLaw
                                  ( NTP4VCCount2 A )
                                  ( NTP4VCCount1 A )
                                  0
                                  2
                                  1
                              )
                              ->
                              (
                                (
                                  0 <_ 2
                                  /\
                                  2 < ( # ` ( NTP4VCSets1 B ) )
                                )
                                /\
                                (
                                  (
                                    # ` ( NTP4VCSets2 B )
                                  ) = ( # ` ( NTP4VCSets1 B ) )
                                  ->
                                  (
                                    (
                                      NTP4VCUpdateLaw
                                        ( NTP4VCSets2 B )
                                        ( NTP4VCSets1 B )
                                        (/)
                                        2
                                        NTP4VCO3
                                    )
                                    ->
                                    (
                                      (
                                        0 <_ 3
                                        /\
                                        3 < (
                                          # ` ( NTP4VCCount2 A )
                                        )
                                      )
                                      /\
                                      (
                                        (
                                          # ` ( NTP4VCCount3 A )
                                        ) = (
                                          # ` ( NTP4VCCount2 A )
                                        )
                                        ->
                                        (
                                          (
                                            NTP4VCUpdateLaw
                                              ( NTP4VCCount3 A )
                                              ( NTP4VCCount2 A )
                                              0
                                              3
                                              2
                                          )
                                          ->
                                          (
                                            (
                                              0 <_ 3
                                              /\
                                              3 < (
                                                # ` ( NTP4VCSets2 B )
                                              )
                                            )
                                            /\
                                            (
                                              (
                                                # ` ( NTP4VCSets3 B )
                                              ) = (
                                                # ` ( NTP4VCSets2 B )
                                              )
                                              ->
                                              (
                                                (
                                                  NTP4VCUpdateLaw
                                                    ( NTP4VCSets3 B )
                                                    ( NTP4VCSets2 B )
                                                    (/)
                                                    3
                                                    NTP4VCO4
                                                )
                                                ->
                                                (
                                                  NTP4VCRun
                                                    ( NTP4VCSets3 B )
                                                    ( NTP4VCCount3 A )
                                                    C
                                                    D
                                                    E
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
) $.

${
  $d i A B C $.

  ntp4vc-enum-vc-definition $a |- (
    NTP4VCEnumVC A B C
  ) <-> (
    0 <_ ; 5 1
    /\
    A. m e. ( Word ZZ )
      (
        (
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i < ; 5 1
                )
                ->
                ( NTP4VCAt m 0 i ) = 0
              )
          )
          /\
          ( # ` m ) = ; 5 1
        )
        ->
        (
          0 <_ ; 5 1
          /\
          A. s e. ( Word NTP4VCColoringSet )
            (
              (
                (
                  A. i e. ZZ
                    (
                      (
                        0 <_ i
                        /\
                        i < ; 5 1
                      )
                      ->
                      ( NTP4VCAt s (/) i ) = (/)
                    )
                )
                /\
                ( # ` s ) = ; 5 1
              )
              ->
              ( NTP4VCInitVC m s A B C )
            )
        )
      )
  ) $.
$}

${
  $d c i j n A B C $.

  $( A=first_black_tile, B=the arbitrary inhabited default color,
     and C=addleft. $)
  ntp4vc-default-color $e |- B e. 2 $.
  ntp4vc-first-black-function
    $e |- A e. ( ZZ ^m ( Word 2 ) ) $.
  ntp4vc-addleft-function
    $e |- C e. ( ( Word 2 ) ^m ( ZZ X. ( Word 2 ) ) ) $.

  ntp4vc-first-black-definition $e |- A. c e. ( Word 2 )
    (
      (
        ( # ` c ) = 0
        ->
        ( A ` c ) = 0
      )
      /\
      (
        0 < ( # ` c )
        ->
        (
          (
            ( NTP4VCAt c B 0 ) = 0
            ->
            ( A ` c ) = 0
          )
          /\
          (
            ( NTP4VCAt c B 0 ) = 1
            ->
            ( A ` c )
            =
            ( 1 + ( A ` ( NTP4VCTail c ) ) )
          )
        )
      )
    ) $.

  ntp4vc-first-black-bounds $e |- A. c e. ( Word 2 )
    (
      0 <_ ( A ` c )
      /\
      ( A ` c ) <_ ( # ` c )
    ) $.

  ntp4vc-first-black-red-prefix $e |- A. c e. ( Word 2 )
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          (
            j < ( A ` c )
            /\
            ( A ` c ) <_ ( # ` c )
          )
        )
        ->
        ( NTP4VCAt c B j ) = 1
      ) $.

  ntp4vc-first-black-at-result $e |- A. c e. ( Word 2 )
    (
      ( A ` c ) < ( # ` c )
      ->
      ( NTP4VCAt c B ( A ` c ) ) = 0
    ) $.

  ntp4vc-first-black-valid-spec $e |- A. c e. ( Word 2 )
    (
      ( NTP4VCValid c B )
      ->
      (
        ( A ` c ) = 0
        \/
        3 <_ ( A ` c )
      )
    ) $.

  ntp4vc-addleft-definition $e |- A. n e. ZZ
    A. c e. ( Word 2 )
      (
        (
          n <_ 0
          ->
          ( C ` <. n , c >. ) = ( <" 0 "> ++ c )
        )
        /\
        (
          0 < n
          ->
          ( C ` <. n , c >. )
          =
          (
            <" 1 ">
            ++
            ( C ` <. ( n - 1 ) , c >. )
          )
        )
      ) $.

  ntp4vc-addleft-length-spec $e |- A. n e. ZZ
    A. c e. ( Word 2 )
      (
        0 <_ n
        ->
        ( # ` ( C ` <. n , c >. ) )
        =
        ( ( # ` c ) + n + 1 )
      ) $.

  ntp4vc-pearl-colored-tiles-enum-vc $a |- (
    NTP4VCEnumVC A B C
  ) $.
$}
