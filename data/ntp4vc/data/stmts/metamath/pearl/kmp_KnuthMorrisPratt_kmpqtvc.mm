$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/kmp_KnuthMorrisPratt_kmpqtvc: the Knuth-Morris-Pratt search
  verification condition initializes and preserves its matching and
  first-occurrence invariant through match, advance, and failure-function
  fallback branches. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  C is the arbitrary inhabited source character carrier, d is its chosen
  default element, Word C is the full type of finite character lists, and
  Word ZZ is the full type of finite integer lists. NTP4VCToNat and
  NTP4VCAt are exactly the source integer-to-natural conversion and totalized
  list lookup.

  NTP4VCMatches, NTP4VCIsNext, and NTP4VCFirstOccur directly encode the
  three source definitions. The remaining predicates only factor the nested
  verification condition. Expanding their biconditional definitions recovers
  every source integer and Boolean quantifier, list-length premise, matching
  condition, maximal proper-prefix clause, loop invariant, decreasing-variant
  disjunction, conditional branch, and final first-occurrence conclusion.
  Booleans are SetMM's exact two-element carrier 2, with false = 0 and
  true = 1. Each proposition-valued conditional is represented by the
  equivalent conjunction of its guarded then and else implications.

  The final $a declaration is Metamath's native unproved statement encoding.
  Every preceding $a declaration is syntax or a faithful definition required
  to state that assertion; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt
  NTP4VCMatches NTP4VCIsNext NTP4VCFirstOccur
  NTP4VCInvariant NTP4VCNextSpec
  NTP4VCMatchStep NTP4VCZeroStep NTP4VCFallbackStep
  NTP4VCThenBranch NTP4VCResultBranch NTP4VCLoop
  NTP4VCKmpVC
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-matches-syntax
  $a wff ( NTP4VCMatches A B C D E F ) $.
ntp4vc-is-next-syntax
  $a wff ( NTP4VCIsNext A B C D ) $.
ntp4vc-first-occur-syntax
  $a wff ( NTP4VCFirstOccur A B C D ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F G ) $.
ntp4vc-next-spec-syntax
  $a wff ( NTP4VCNextSpec A B C ) $.
ntp4vc-match-step-syntax
  $a wff ( NTP4VCMatchStep A B C D E F G ) $.
ntp4vc-zero-step-syntax
  $a wff ( NTP4VCZeroStep A B C D E F G ) $.
ntp4vc-fallback-step-syntax
  $a wff ( NTP4VCFallbackStep A B C D E F G H ) $.
ntp4vc-then-branch-syntax
  $a wff ( NTP4VCThenBranch A B C D E F G H ) $.
ntp4vc-result-branch-syntax
  $a wff ( NTP4VCResultBranch A B C D E F ) $.
ntp4vc-loop-syntax
  $a wff ( NTP4VCLoop A B C D E F ) $.
ntp4vc-kmp-vc-syntax
  $a wff ( NTP4VCKmpVC A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 < A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  C
) $.

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

  ntp4vc-first-occur-definition $a |- (
    NTP4VCFirstOccur A B C D
  ) <-> (
    (
      (
        0 <_ C
        /\
        C < ( # ` B )
      )
      ->
      (
        NTP4VCMatches
          B C A 0 ( # ` A ) D
      )
    )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < C
        )
        ->
        -.
        (
          NTP4VCMatches
            B k A 0 ( # ` A ) D
        )
      )
  ) $.
$}

${
  $d k A B C D E F G $.

  $(
    A=a, B=p, C=m, D=n, E=j, F=i, and G is the default character.
  $)
  ntp4vc-invariant-definition $a |- (
    NTP4VCInvariant A B C D E F G
  ) <-> (
    (
      (
        (
          0 <_ E
          /\
          E <_ C
        )
        /\
        (
          E <_ F
          /\
          F <_ D
        )
      )
      /\
      ( NTP4VCMatches A ( F - E ) B 0 E G )
    )
    /\
    A. k e. ZZ
      (
        (
          0 <_ k
          /\
          k < ( F - E )
        )
        ->
        -.
        ( NTP4VCMatches A k B 0 C G )
      )
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-next-spec-definition $a |- (
    NTP4VCNextSpec A B C
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

ntp4vc-match-step-definition $a |- (
  NTP4VCMatchStep A B C D E F G
) <-> (
  (
    (
      0 <_ ( D - F )
      /\
      ( D - ( F + 1 ) ) < ( D - F )
    )
    \/
    (
      ( D - F ) = ( D - ( F + 1 ) )
      /\
      (
        0 <_ E
        /\
        ( E + 1 ) < E
      )
    )
  )
  /\
  (
    NTP4VCInvariant
      A B C D ( E + 1 ) ( F + 1 ) G
  )
) $.

ntp4vc-zero-step-definition $a |- (
  NTP4VCZeroStep A B C D E F G
) <-> (
  (
    (
      0 <_ ( D - F )
      /\
      ( D - ( F + 1 ) ) < ( D - F )
    )
    \/
    (
      ( D - F ) = ( D - ( F + 1 ) )
      /\
      (
        0 <_ E
        /\
        E < E
      )
    )
  )
  /\
  (
    NTP4VCInvariant
      A B C D E ( F + 1 ) G
  )
) $.

ntp4vc-fallback-step-definition $a |- (
  NTP4VCFallbackStep A B C D E F G H
) <-> (
  (
    0 <_ F
    /\
    F < ( # ` C )
  )
  /\
  (
    (
      (
        0 <_ ( E - G )
        /\
        ( E - G ) < ( E - G )
      )
      \/
      (
        0 <_ F
        /\
        ( NTP4VCAt C F 0 ) < F
      )
    )
    /\
    (
      NTP4VCInvariant
        A B D E ( NTP4VCAt C F 0 ) G H
    )
  )
) $.

ntp4vc-then-branch-definition $a |- (
  NTP4VCThenBranch A B C D E F G H
) <-> (
  (
    0 <_ F
    /\
    F < ( # ` B )
  )
  /\
  (
    (
      0 <_ G
      /\
      G < ( # ` A )
    )
    /\
    (
      (
        (
          NTP4VCAt A G H
        )
        =
        (
          NTP4VCAt B F H
        )
        ->
        (
          NTP4VCMatchStep
            A B D E F G H
        )
      )
      /\
      (
        (
          NTP4VCAt A G H
        )
        =/=
        (
          NTP4VCAt B F H
        )
        ->
        (
          (
            F = 0
            ->
            (
              NTP4VCZeroStep
                A B D E F G H
            )
          )
          /\
          (
            F =/= 0
            ->
            (
              NTP4VCFallbackStep
                A B C D E F G H
            )
          )
        )
      )
    )
  )
) $.

${
  $d r A B C D E F $.

  $(
    A=p, B=a, C=m, D=j, E=i, and F is the default character.
  $)
  ntp4vc-result-branch-definition $a |- (
    NTP4VCResultBranch A B C D E F
  ) <-> (
    A. r e. ZZ
      (
        r = if (
          D = C ,
          ( E - C ) ,
          E
        )
        ->
        (
          NTP4VCFirstOccur A B r F
        )
      )
  ) $.
$}

${
  $d i j o A B C D E F $.

  $(
    A=a, B=p, C=next, D=m, E=n, and F is the default character.
  $)
  ntp4vc-loop-definition $a |- (
    NTP4VCLoop A B C D E F
  ) <-> (
    A. j e. ZZ
      A. i e. ZZ
        (
          ( NTP4VCInvariant A B D E j i F )
          ->
          A. o e. { 0 , 1 }
            (
              o = if (
                j < D ,
                if (
                  i < E ,
                  1 ,
                  0
                ) ,
                0
              )
              ->
              (
                (
                  o = 1
                  ->
                  (
                    NTP4VCThenBranch
                      A B C D E j i F
                  )
                )
                /\
                (
                  o =/= 1
                  ->
                  (
                    NTP4VCResultBranch
                      B A D j i F
                  )
                )
              )
            )
        )
  ) $.
$}

${
  $d t A B C $.

  ntp4vc-kmp-vc-definition $a |- (
    NTP4VCKmpVC A B C
  ) <-> (
    1 <_ ( # ` A )
    /\
    A. t e. Word ZZ
      (
        ( NTP4VCNextSpec A t C )
        ->
        (
          (
            NTP4VCInvariant
              B A ( # ` A ) ( # ` B ) 0 0 C
          )
          /\
          (
            NTP4VCLoop
              B A t ( # ` A ) ( # ` B ) C
          )
        )
      )
  ) $.
$}

${
  $d A B C D $.

  $( The arbitrary inhabited source character type and its default element. $)
  ntp4vc-char-carrier-set $e |- D e. _V $.
  ntp4vc-default-character $e |- C e. D $.

  $( Source theorem parameters p and a, and assumption fact0. $)
  ntp4vc-pattern-word $e |- A e. Word D $.
  ntp4vc-text-word $e |- B e. Word D $.
  ntp4vc-fact0 $e |- 1 <_ ( # ` A ) $.

  ntp4vc-pearl-kmp-knuth-morris-pratt-kmp-vc
    $a |- ( NTP4VCKmpVC A B C ) $.
$}
