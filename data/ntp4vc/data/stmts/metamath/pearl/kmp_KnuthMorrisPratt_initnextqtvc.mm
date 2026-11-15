$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_initnextqtvc: the Knuth-Morris-Pratt
  initialization verification condition maintains the maximal proper-prefix
  failure-function invariant through initialization and loop updates and
  establishes it for every positive pattern position. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  C is the arbitrary inhabited source character carrier, d is its chosen
  default element, Word C is the full type of finite character lists, and
  Word ZZ is the full type of finite integer lists.

  NTP4VCToNat, NTP4VCAt, and NTP4VCSet are exactly the source integer-to-
  natural conversion, totalized list lookup, and list update. The remaining
  named predicates factor the source definitions and nested verification
  condition. Expanding their biconditional definitions recovers every source
  integer bound, list-length premise, universal quantifier, update-law
  premise, conditional branch, matching predicate, maximality clause, loop
  invariant, and final failure-function conclusion. Each proposition-valued
  conditional is represented by the equivalent conjunction of its guarded
  then and else implications.

  The final $a declaration is Metamath's native unproved statement encoding.
  Every preceding $a declaration is syntax or a faithful definition required
  to state that assertion; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet
  NTP4VCBound NTP4VCUpdateLaw NTP4VCZeroes
  NTP4VCMatches NTP4VCIsNext NTP4VCPrefix NTP4VCFinal
  NTP4VCLoopInv NTP4VCEqStep NTP4VCZeroStep NTP4VCFallbackStep
  NTP4VCBody NTP4VCLoop NTP4VCOuter NTP4VCInitNextVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.

ntp4vc-bound-syntax $a wff ( NTP4VCBound A B ) $.
ntp4vc-update-law-syntax $a wff ( NTP4VCUpdateLaw A B C ) $.
ntp4vc-zeroes-syntax $a wff ( NTP4VCZeroes A B ) $.
ntp4vc-matches-syntax
  $a wff ( NTP4VCMatches A B C D E F ) $.
ntp4vc-is-next-syntax $a wff ( NTP4VCIsNext A B C D ) $.
ntp4vc-prefix-syntax $a wff ( NTP4VCPrefix A B C D ) $.
ntp4vc-final-syntax $a wff ( NTP4VCFinal A B C ) $.
ntp4vc-loop-inv-syntax
  $a wff ( NTP4VCLoopInv A B C D E F ) $.
ntp4vc-eq-step-syntax
  $a wff ( NTP4VCEqStep A B C D E F ) $.
ntp4vc-zero-step-syntax
  $a wff ( NTP4VCZeroStep A B C D E F ) $.
ntp4vc-fallback-step-syntax
  $a wff ( NTP4VCFallbackStep A B C D E F ) $.
ntp4vc-body-syntax $a wff ( NTP4VCBody A B C D E F ) $.
ntp4vc-loop-syntax $a wff ( NTP4VCLoop A B C D ) $.
ntp4vc-outer-syntax $a wff ( NTP4VCOuter A B C D ) $.
ntp4vc-init-next-vc-syntax $a wff ( NTP4VCInitNextVC A B ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if ( 0 <_ A , A , 0 ) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
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

ntp4vc-bound-definition $a |- (
  NTP4VCBound A B
) <-> (
  0 <_ B
  /\
  B < ( # ` A )
) $.

${
  $d k A B C $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C
  ) <-> (
    A. k e. ZZ
      (
        ( NTP4VCAt ( NTP4VCSet A B C ) k 0 )
        =
        if (
          k = B ,
          C ,
          ( NTP4VCAt A k 0 )
        )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-zeroes-definition $a |- (
    NTP4VCZeroes A B
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAt A i 0 ) = 0
      )
  ) $.
$}

${
  $d i A B C D E F $.

  ntp4vc-matches-definition $a |- (
    NTP4VCMatches A B C D E F
  ) <-> (
    (
      0 <_ B
      /\
      B <_ ( ( # ` A ) - E )
    )
    /\
    (
      (
        0 <_ D
        /\
        D <_ ( ( # ` C ) - E )
      )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < E
          )
          ->
          (
            NTP4VCAt A ( B + i ) F
          )
          =
          (
            NTP4VCAt C ( D + i ) F
          )
        )
    )
  ) $.
$}

${
  $d z A B C D $.

  ntp4vc-is-next-definition $a |- (
    NTP4VCIsNext A B C D
  ) <-> (
    (
      0 <_ C
      /\
      C < B
    )
    /\
    (
      ( NTP4VCMatches A ( B - C ) A 0 C D )
      /\
      A. z e. ZZ
        (
          (
            C < z
            /\
            z < B
          )
          ->
          -.
          ( NTP4VCMatches A ( B - z ) A 0 z D )
        )
    )
  ) $.
$}

${
  $d k A B C D $.

  ntp4vc-prefix-definition $a |- (
    NTP4VCPrefix A B C D
  ) <-> (
    A. k e. ZZ
      (
        (
          0 < k
          /\
          k <_ C
        )
        ->
        (
          NTP4VCIsNext
            A
            k
            ( NTP4VCAt B k 0 )
            D
        )
      )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-final-definition $a |- (
    NTP4VCFinal A B C
  ) <-> (
    ( # ` B ) = ( # ` A )
    /\
    A. j e. ZZ
      (
        (
          0 < j
          /\
          j < ( # ` A )
        )
        ->
        (
          NTP4VCIsNext
            A
            j
            ( NTP4VCAt B j 0 )
            C
        )
      )
  ) $.
$}

${
  $d z A B C D E F $.

  ntp4vc-loop-inv-definition $a |- (
    NTP4VCLoopInv A B C D E F
  ) <-> (
    (
      0 <_ D
      /\
      (
        D < E
        /\
        E <_ C
      )
    )
    /\
    (
      ( NTP4VCMatches A ( E - D ) A 0 D B )
      /\
      (
        A. z e. ZZ
          (
            (
              ( D + 1 ) < z
              /\
              z < ( E + 1 )
            )
            ->
            -.
            (
              NTP4VCMatches
                A
                ( ( E + 1 ) - z )
                A
                0
                z
                B
            )
          )
        /\
        ( NTP4VCPrefix A F E B )
      )
    )
  ) $.
$}

ntp4vc-eq-step-definition $a |- (
  NTP4VCEqStep A B C D E F
) <-> (
  ( NTP4VCBound F ( E + 1 ) )
  /\
  (
    (
      #
      `
      (
        NTP4VCSet F ( E + 1 ) ( D + 1 )
      )
    )
    =
    ( # ` F )
    ->
    (
      ( NTP4VCUpdateLaw F ( E + 1 ) ( D + 1 ) )
      ->
      (
        (
          (
            0 <_ ( C - E )
            /\
            ( C - ( E + 1 ) ) < ( C - E )
          )
          \/
          (
            ( C - E ) = ( C - ( E + 1 ) )
            /\
            (
              0 <_ D
              /\
              ( D + 1 ) < D
            )
          )
        )
        /\
        (
          NTP4VCLoopInv
            A
            B
            C
            ( D + 1 )
            ( E + 1 )
            (
              NTP4VCSet F ( E + 1 ) ( D + 1 )
            )
        )
      )
    )
  )
) $.

ntp4vc-zero-step-definition $a |- (
  NTP4VCZeroStep A B C D E F
) <-> (
  ( NTP4VCBound F ( E + 1 ) )
  /\
  (
    (
      #
      `
      (
        NTP4VCSet F ( E + 1 ) 0
      )
    )
    =
    ( # ` F )
    ->
    (
      ( NTP4VCUpdateLaw F ( E + 1 ) 0 )
      ->
      (
        (
          (
            0 <_ ( C - E )
            /\
            ( C - ( E + 1 ) ) < ( C - E )
          )
          \/
          (
            ( C - E ) = ( C - ( E + 1 ) )
            /\
            (
              0 <_ D
              /\
              D < D
            )
          )
        )
        /\
        (
          NTP4VCLoopInv
            A
            B
            C
            D
            ( E + 1 )
            ( NTP4VCSet F ( E + 1 ) 0 )
        )
      )
    )
  )
) $.

ntp4vc-fallback-step-definition $a |- (
  NTP4VCFallbackStep A B C D E F
) <-> (
  ( NTP4VCBound F D )
  /\
  (
    (
      (
        0 <_ ( C - E )
        /\
        ( C - E ) < ( C - E )
      )
      \/
      (
        0 <_ D
        /\
        ( NTP4VCAt F D 0 ) < D
      )
    )
    /\
    (
      NTP4VCLoopInv
        A
        B
        C
        ( NTP4VCAt F D 0 )
        E
        F
    )
  )
) $.

ntp4vc-body-definition $a |- (
  NTP4VCBody A B C D E F
) <-> (
  (
    E < ( C - 1 )
    ->
    (
      ( NTP4VCBound A D )
      /\
      (
        ( NTP4VCBound A E )
        /\
        (
          (
            ( NTP4VCAt A E B )
            =
            ( NTP4VCAt A D B )
          )
          ->
          ( NTP4VCEqStep A B C D E F )
        )
        /\
        (
          -.
          (
            ( NTP4VCAt A E B )
            =
            ( NTP4VCAt A D B )
          )
          ->
          (
            (
              D = 0
              ->
              ( NTP4VCZeroStep A B C D E F )
            )
            /\
            (
              D =/= 0
              ->
              ( NTP4VCFallbackStep A B C D E F )
            )
          )
        )
      )
    )
  )
  /\
  (
    -. E < ( C - 1 )
    ->
    ( NTP4VCFinal A F B )
  )
) $.

${
  $d i j t A B C D $.

  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D
  ) <-> (
    A. j e. ZZ
      A. i e. ZZ
        A. t e. Word ZZ
          (
            ( # ` t ) = ( # ` D )
            ->
            (
              ( NTP4VCLoopInv A B C j i t )
              ->
              ( NTP4VCBody A B C j i t )
            )
          )
  ) $.
$}

ntp4vc-outer-definition $a |- (
  NTP4VCOuter A B C D
) <-> (
  (
    1 < C
    ->
    (
      ( NTP4VCBound D 1 )
      /\
      (
        (
          # ` ( NTP4VCSet D 1 0 )
        )
        =
        ( # ` D )
        ->
        (
          ( NTP4VCUpdateLaw D 1 0 )
          ->
          (
            (
              NTP4VCLoopInv
                A
                B
                C
                0
                1
                ( NTP4VCSet D 1 0 )
            )
            /\
            (
              NTP4VCLoop
                A
                B
                C
                ( NTP4VCSet D 1 0 )
            )
          )
        )
      )
    )
  )
  /\
  (
    -. 1 < C
    ->
    ( NTP4VCFinal A D B )
  )
) $.

${
  $d t A B $.

  ntp4vc-init-next-vc-definition $a |- (
    NTP4VCInitNextVC A B
  ) <-> (
    0 <_ ( # ` A )
    /\
    A. t e. Word ZZ
      (
        (
          ( NTP4VCZeroes t ( # ` A ) )
          /\
          ( # ` t ) = ( # ` A )
        )
        ->
        (
          NTP4VCOuter
            A
            B
            ( # ` A )
            t
        )
      )
  ) $.
$}

${
  $d A B C $.

  $( The arbitrary inhabited source character type and its default element. $)
  ntp4vc-char-carrier-set $e |- C e. _V $.
  ntp4vc-default-character $e |- B e. C $.

  $( Source theorem parameter p and assumption fact0. $)
  ntp4vc-pattern-word $e |- A e. Word C $.
  ntp4vc-fact0 $e |- 1 <_ ( # ` A ) $.

  ntp4vc-pearl-kmp-knuth-morris-pratt-initnext-vc
    $a |- ( NTP4VCInitNextVC A B ) $.
$}
