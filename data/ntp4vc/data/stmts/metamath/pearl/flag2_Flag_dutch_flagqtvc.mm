$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/flag2_Flag_dutch_flagqtvc: the Dutch-national-flag verification
  condition states initialization, invariant preservation, variant decrease,
  color-segment partitioning, and occurrence preservation for the Blue,
  White, and Red loop branches. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source datatype color is represented exactly by the three-element set
  0 through 2, with Blue = 0, White = 1, and Red = 2. Color lists are SetMM
  words over this carrier, hence arbitrary finite zero-based color sequences.
  NTP4VCToNat is the source integer-to-natural conversion and NTP4VCAt is the
  source totalized lookup, parameterized by the source's arbitrary inhabited
  default color.

  NTP4VCOcc is the cardinality of matching positions in a half-open integer
  interval. This is bidirectionally equivalent to the source nb_occ together
  with nb_occ'def: the empty/reversed interval has count zero, and extending a
  nonempty interval by its last position gives exactly the displayed recursive
  equation; conversely that equation uniquely determines the same finite
  cardinality by induction on the interval length.

  The remaining named predicates only factor the source invariant, swap
  premises, three color branches, and terminating partition. Proposition-valued
  conditionals and the color match are rendered as exhaustive guarded
  disjunctions. Bundled conjunction premises are equivalent in both directions
  to the source's curried implications. Every list, integer, and color
  quantifier retains its full source domain, and the existential partition
  boundaries remain internal to the terminating branch. The final declaration
  is Metamath's native unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

$c
  NTP4VCColor NTP4VCToNat NTP4VCAt NTP4VCOcc NTP4VCMono
  NTP4VCCounts NTP4VCInvariant NTP4VCUnchanged NTP4VCOccPres
  NTP4VCSwapPrem NTP4VCBlueResult NTP4VCWhiteResult
  NTP4VCRedResult NTP4VCBlueBranch NTP4VCWhiteBranch
  NTP4VCRedBranch NTP4VCStep NTP4VCFinish NTP4VCBody
  NTP4VCInitial
$.

ntp4vc-color-syntax $a class NTP4VCColor $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B C ) $.
ntp4vc-occ-syntax $a class ( NTP4VCOcc A B C D E ) $.
ntp4vc-mono-syntax $a wff ( NTP4VCMono A B C D E ) $.
ntp4vc-counts-syntax $a wff ( NTP4VCCounts A B C ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F ) $.
ntp4vc-unchanged-syntax
  $a wff ( NTP4VCUnchanged A B C D E ) $.
ntp4vc-occ-pres-syntax
  $a wff ( NTP4VCOccPres A B C D E ) $.
ntp4vc-swap-prem-syntax
  $a wff ( NTP4VCSwapPrem A B C D E ) $.
ntp4vc-blue-result-syntax
  $a wff ( NTP4VCBlueResult A B C D E F ) $.
ntp4vc-white-result-syntax
  $a wff ( NTP4VCWhiteResult A B C D E F ) $.
ntp4vc-red-result-syntax
  $a wff ( NTP4VCRedResult A B C D E F ) $.
ntp4vc-blue-branch-syntax
  $a wff ( NTP4VCBlueBranch A B C D E F ) $.
ntp4vc-white-branch-syntax
  $a wff ( NTP4VCWhiteBranch A B C D E F ) $.
ntp4vc-red-branch-syntax
  $a wff ( NTP4VCRedBranch A B C D E F ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C ) $.
ntp4vc-body-syntax
  $a wff ( NTP4VCBody A B C D E F ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B ) $.

ntp4vc-color-definition $a |- NTP4VCColor = ( 0 ... 2 ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B C
) = if (
  ( NTP4VCToNat C ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat C ) ) ,
  B
) $.

${
  $d k A B C D E $.

  ntp4vc-occ-definition $a |- (
    NTP4VCOcc A B C D E
  ) = (
    # `
    { k e. ( C ..^ D ) | ( NTP4VCAt A B k ) = E }
  ) $.
$}

${
  $d k A B C D E $.

  ntp4vc-mono-definition $a |- (
    ( NTP4VCMono A B C D E )
    <->
    A. k e. ZZ
      (
        (
          C <_ k
          /\
          k < D
        )
        ->
        ( NTP4VCAt A B k ) = E
      )
  ) $.
$}

${
  $d c A B C $.

  ntp4vc-counts-definition $a |- (
    ( NTP4VCCounts A B C )
    <->
    A. c e. NTP4VCColor
      (
        ( NTP4VCOcc A C 0 ( # ` A ) c )
        =
        ( NTP4VCOcc B C 0 ( # ` A ) c )
      )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  ( NTP4VCInvariant A B C D E F )
  <->
  (
    (
      0 <_ D
      /\
      (
        D <_ E
        /\
        (
          E <_ F
          /\
          F <_ ( # ` A )
        )
      )
    )
    /\
    (
      ( NTP4VCMono A C 0 D 0 )
      /\
      (
        ( NTP4VCMono A C D E 1 )
        /\
        (
          ( NTP4VCMono A C F ( # ` A ) 2 )
          /\
          ( NTP4VCCounts A B C )
        )
      )
    )
  )
) $.

${
  $d k A B C D E $.

  ntp4vc-unchanged-definition $a |- (
    ( NTP4VCUnchanged A B C D E )
    <->
    A. k e. ZZ
      (
        (
          k =/= D
          /\
          k =/= E
        )
        ->
        ( NTP4VCAt B C k ) = ( NTP4VCAt A C k )
      )
  ) $.
$}

${
  $d x y c A B C D E $.

  ntp4vc-occ-pres-definition $a |- (
    ( NTP4VCOccPres A B C D E )
    <->
    A. x e. ZZ A. y e. ZZ A. c e. NTP4VCColor
      (
        (
          (
            x <_ D
            /\
            D < y
          )
          /\
          (
            x <_ E
            /\
            E < y
          )
        )
        ->
        (
          NTP4VCOcc B C x y c
        ) = (
          NTP4VCOcc A C x y c
        )
      )
  ) $.
$}

ntp4vc-swap-prem-definition $a |- (
  ( NTP4VCSwapPrem A B C D E )
  <->
  (
    ( # ` B ) = ( # ` A )
    /\
    (
      ( NTP4VCAt B C D ) = ( NTP4VCAt A C E )
      /\
      (
        ( NTP4VCAt B C E ) = ( NTP4VCAt A C D )
        /\
        (
          ( NTP4VCUnchanged A B C D E )
          /\
          ( NTP4VCOccPres A B C D E )
        )
      )
    )
  )
) $.

ntp4vc-blue-result-definition $a |- (
  ( NTP4VCBlueResult A B C D E F )
  <->
  (
    (
      0 <_ ( F - E )
      /\
      ( F - ( E + 1 ) ) < ( F - E )
    )
    /\
    (
      (
        0 <_ ( D + 1 )
        /\
        (
          ( D + 1 ) <_ ( E + 1 )
          /\
          (
            ( E + 1 ) <_ F
            /\
            F <_ ( # ` A )
          )
        )
      )
      /\
      (
        ( NTP4VCMono A C 0 ( D + 1 ) 0 )
        /\
        (
          ( NTP4VCMono A C ( D + 1 ) ( E + 1 ) 1 )
          /\
          (
            ( NTP4VCMono A C F ( # ` A ) 2 )
            /\
            ( NTP4VCCounts A B C )
          )
        )
      )
    )
  )
) $.

ntp4vc-white-result-definition $a |- (
  ( NTP4VCWhiteResult A B C D E F )
  <->
  (
    (
      0 <_ ( F - E )
      /\
      ( F - ( E + 1 ) ) < ( F - E )
    )
    /\
    (
      (
        0 <_ D
        /\
        (
          D <_ ( E + 1 )
          /\
          (
            ( E + 1 ) <_ F
            /\
            F <_ ( # ` A )
          )
        )
      )
      /\
      (
        ( NTP4VCMono A C 0 D 0 )
        /\
        (
          ( NTP4VCMono A C D ( E + 1 ) 1 )
          /\
          (
            ( NTP4VCMono A C F ( # ` A ) 2 )
            /\
            ( NTP4VCCounts A B C )
          )
        )
      )
    )
  )
) $.

ntp4vc-red-result-definition $a |- (
  ( NTP4VCRedResult A B C D E F )
  <->
  (
    (
      0 <_ ( F - E )
      /\
      ( ( F - 1 ) - E ) < ( F - E )
    )
    /\
    (
      (
        0 <_ D
        /\
        (
          D <_ E
          /\
          (
            E <_ ( F - 1 )
            /\
            ( F - 1 ) <_ ( # ` A )
          )
        )
      )
      /\
      (
        ( NTP4VCMono A C 0 D 0 )
        /\
        (
          ( NTP4VCMono A C D E 1 )
          /\
          (
            ( NTP4VCMono A C ( F - 1 ) ( # ` A ) 2 )
            /\
            ( NTP4VCCounts A B C )
          )
        )
      )
    )
  )
) $.

${
  $d s A B C D E F $.

  ntp4vc-blue-branch-definition $a |- (
    ( NTP4VCBlueBranch A B C D E F )
    <->
    (
      (
        (
          0 <_ D
          /\
          D < ( # ` A )
        )
        /\
        (
          0 <_ E
          /\
          E < ( # ` A )
        )
      )
      /\
      A. s e. ( Word NTP4VCColor )
        (
          ( NTP4VCSwapPrem A s C D E )
          ->
          ( NTP4VCBlueResult s B C D E F )
        )
    )
  ) $.
$}

ntp4vc-white-branch-definition $a |- (
  ( NTP4VCWhiteBranch A B C D E F )
  <->
  ( NTP4VCWhiteResult A B C D E F )
) $.

${
  $d s A B C D E F $.

  ntp4vc-red-branch-definition $a |- (
    ( NTP4VCRedBranch A B C D E F )
    <->
    (
      (
        (
          0 <_ ( F - 1 )
          /\
          ( F - 1 ) < ( # ` A )
        )
        /\
        (
          0 <_ E
          /\
          E < ( # ` A )
        )
      )
      /\
      A. s e. ( Word NTP4VCColor )
        (
          ( NTP4VCSwapPrem A s C ( F - 1 ) E )
          ->
          ( NTP4VCRedResult s B C D E F )
        )
    )
  ) $.
$}

ntp4vc-step-definition $a |- (
  ( NTP4VCStep A B C D E F )
  <->
  (
    (
      0 <_ E
      /\
      E < ( # ` A )
    )
    /\
    (
      (
        ( NTP4VCAt A C E ) = 0
        /\
        ( NTP4VCBlueBranch A B C D E F )
      )
      \/
      (
        (
          ( NTP4VCAt A C E ) = 1
          /\
          ( NTP4VCWhiteBranch A B C D E F )
        )
        \/
        (
          ( NTP4VCAt A C E ) = 2
          /\
          ( NTP4VCRedBranch A B C D E F )
        )
      )
    )
  )
) $.

${
  $d b r A B C $.

  ntp4vc-finish-definition $a |- (
    ( NTP4VCFinish A B C )
    <->
    (
      E. b e. ZZ E. r e. ZZ
        (
          ( NTP4VCMono A C 0 b 0 )
          /\
          (
            ( NTP4VCMono A C b r 1 )
            /\
            ( NTP4VCMono A C r ( # ` A ) 2 )
          )
        )
      /\
      ( NTP4VCCounts A B C )
    )
  ) $.
$}

ntp4vc-body-definition $a |- (
  ( NTP4VCBody A B C D E F )
  <->
  (
    (
      E < F
      /\
      ( NTP4VCStep A B C D E F )
    )
    \/
    (
      -. E < F
      /\
      ( NTP4VCFinish A B C )
    )
  )
) $.

ntp4vc-initial-definition $a |- (
  ( NTP4VCInitial A B )
  <->
  (
    (
      0 <_ 0
      /\
      (
        0 <_ 0
        /\
        (
          0 <_ ( # ` A )
          /\
          ( # ` A ) <_ ( # ` A )
        )
      )
    )
    /\
    (
      ( NTP4VCMono A B 0 0 0 )
      /\
      (
        ( NTP4VCMono A B 0 0 1 )
        /\
        ( NTP4VCMono A B ( # ` A ) ( # ` A ) 2 )
      )
    )
  )
) $.

${
  $d r i b s A B $.

  $( Source theorem parameter A=a and source inhabited default B. $)

  ntp4vc-a-color-list
    $e |- A e. ( Word NTP4VCColor ) $.
  ntp4vc-default-color
    $e |- B e. NTP4VCColor $.

  ntp4vc-pearl-flag2-dutch-flag-vc $a |- (
    ( NTP4VCInitial A B )
    /\
    A. r e. ZZ A. i e. ZZ A. b e. ZZ
      A. s e. ( Word NTP4VCColor )
        (
          ( # ` s ) = ( # ` A )
          ->
          (
            ( NTP4VCInvariant s A B b i r )
            ->
            ( NTP4VCBody s A B b i r )
          )
        )
  ) $.
$}
