$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/word_common_factor_Top_common_factorqtvc: the common-factor
  verification condition for two commuting finite words, establishing the
  recursive length descent and that both words are nonnegative powers of a
  common word. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  D is the arbitrary nonempty character carrier, and Word D is exactly the
  full type of arbitrary finite character words. A is the source power
  function, uncurried to a total function on Word D X. ZZ. Its scoped
  recursion hypothesis is exactly the source equation for every nonnegative
  integer exponent.

  NTP4VCDrop is the zero-based suffix after the given nonnegative index.
  Every use supplies the length of a word, so it agrees exactly with the
  source integer-to-natural conversion and list drop. The source let-bindings
  for lengths and suffixes are expanded definitionally.

  Proposition-valued conditionals are represented by exhaustive guarded
  implications. NTP4VCDescent retains the generated lexicographic descent
  obligation. NTP4VCResultPremise retains the empty-word cases and recursive
  branch, including the internal existential exponent for the suffix.
  NTP4VCResult universally quantifies the common word and both integer
  exponents at their original scope.

  Splitting the arbitrary carrier, power model, theorem parameters, recursion
  law, and commuting-word premise into scoped essential hypotheses is
  equivalent to the source curried statement. Every auxiliary $a declaration
  below is syntax or an explicit faithful definition. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p declaration.
$)

$c
  NTP4VCPower NTP4VCDrop
  NTP4VCShortBranch NTP4VCLongBranch NTP4VCDescent
  NTP4VCPowerConclusion
  NTP4VCShortPremise NTP4VCLongPremise NTP4VCResultPremise
  NTP4VCResult NTP4VCMain
$.

ntp4vc-power-syntax
  $a class ( NTP4VCPower A B C ) $.
ntp4vc-drop-syntax
  $a class ( NTP4VCDrop A B ) $.
ntp4vc-short-branch-syntax
  $a wff ( NTP4VCShortBranch A B ) $.
ntp4vc-long-branch-syntax
  $a wff ( NTP4VCLongBranch A B ) $.
ntp4vc-descent-syntax
  $a wff ( NTP4VCDescent A B ) $.
ntp4vc-power-conclusion-syntax
  $a wff ( NTP4VCPowerConclusion A B C D E F ) $.
ntp4vc-short-premise-syntax
  $a wff ( NTP4VCShortPremise A B C D E F ) $.
ntp4vc-long-premise-syntax
  $a wff ( NTP4VCLongPremise A B C D E F ) $.
ntp4vc-result-premise-syntax
  $a wff ( NTP4VCResultPremise A B C D E F ) $.
ntp4vc-result-syntax
  $a wff ( NTP4VCResult A B C D ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B C D ) $.

ntp4vc-power-definition $a |- (
  NTP4VCPower A B C
) = (
  A ` <. B , C >.
) $.

${
  $d k A B $.

  ntp4vc-drop-definition $a |- (
    NTP4VCDrop A B
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) - B ) )
    |-> ( A ` ( k + B ) )
  ) $.
$}

ntp4vc-short-branch-definition $a |- (
  NTP4VCShortBranch A B
) <-> (
  (
    0 <_ ( # ` A )
    /\
    ( # ` A ) <_ ( # ` B )
  )
  /\
  (
    B = ( A ++ ( NTP4VCDrop B ( # ` A ) ) )
    /\
    (
      B = ( A ++ ( NTP4VCDrop B ( # ` A ) ) )
      ->
      (
        (
          0 <_ ( # ` B )
          /\
          ( # ` ( NTP4VCDrop B ( # ` A ) ) ) < ( # ` B )
        )
        /\
        (
          A ++ ( NTP4VCDrop B ( # ` A ) )
        ) = (
          ( NTP4VCDrop B ( # ` A ) ) ++ A
        )
      )
    )
  )
) $.

ntp4vc-long-branch-definition $a |- (
  NTP4VCLongBranch A B
) <-> (
  (
    (
      0 <_ ( # ` A )
      /\
      ( # ` B ) < ( # ` A )
    )
    \/
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        0 <_ ( # ` B )
        /\
        ( # ` A ) < ( # ` B )
      )
    )
  )
  /\
  ( B ++ A ) = ( A ++ B )
) $.

ntp4vc-descent-definition $a |- (
  NTP4VCDescent A B
) <-> (
  ( # ` A ) =/= 0
  ->
  (
    ( # ` B ) =/= 0
    ->
    (
      (
        ( # ` A ) <_ ( # ` B )
        ->
        ( NTP4VCShortBranch A B )
      )
      /\
      (
        -. ( ( # ` A ) <_ ( # ` B ) )
        ->
        ( NTP4VCLongBranch A B )
      )
    )
  )
) $.

ntp4vc-power-conclusion-definition $a |- (
  NTP4VCPowerConclusion A B C D E F
) <-> (
  (
    0 <_ E
    /\
    B = ( NTP4VCPower A D E )
  )
  /\
  (
    0 <_ F
    /\
    C = ( NTP4VCPower A D F )
  )
) $.

${
  $d k A B C D E F $.

  ntp4vc-short-premise-definition $a |- (
    NTP4VCShortPremise A B C D E F
  ) <-> (
    C = ( B ++ ( NTP4VCDrop C ( # ` B ) ) )
    /\
    E. k e. ZZ
      (
        (
          (
            0 <_ E
            /\
            B = ( NTP4VCPower A D E )
          )
          /\
          (
            0 <_ k
            /\
            ( NTP4VCDrop C ( # ` B ) )
              = ( NTP4VCPower A D k )
          )
        )
        /\
        F = ( E + k )
      )
  ) $.
$}

ntp4vc-long-premise-definition $a |- (
  NTP4VCLongPremise A B C D E F
) <-> (
  (
    0 <_ F
    /\
    C = ( NTP4VCPower A D F )
  )
  /\
  (
    0 <_ E
    /\
    B = ( NTP4VCPower A D E )
  )
) $.

ntp4vc-result-premise-definition $a |- (
  NTP4VCResultPremise A B C D E F
) <-> (
  (
    ( # ` B ) = 0
    ->
    (
      D = C
      /\
      (
        E = 0
        /\
        F = 1
      )
    )
  )
  /\
  (
    ( # ` B ) =/= 0
    ->
    (
      (
        ( # ` C ) = 0
        ->
        (
          D = B
          /\
          (
            E = 1
            /\
            F = 0
          )
        )
      )
      /\
      (
        ( # ` C ) =/= 0
        ->
        (
          (
            ( # ` B ) <_ ( # ` C )
            ->
            ( NTP4VCShortPremise A B C D E F )
          )
          /\
          (
            -. ( ( # ` B ) <_ ( # ` C ) )
            ->
            ( NTP4VCLongPremise A B C D E F )
          )
        )
      )
    )
  )
) $.

${
  $d w i j A B C D $.

  ntp4vc-result-definition $a |- (
    NTP4VCResult A B C D
  ) <-> (
    A. w e. Word D
      A. i e. ZZ
        A. j e. ZZ
          (
            ( NTP4VCResultPremise A B C w i j )
            ->
            ( NTP4VCPowerConclusion A B C w i j )
          )
  ) $.
$}

ntp4vc-main-definition $a |- (
  NTP4VCMain A B C D
) <-> (
  ( NTP4VCDescent B C )
  /\
  ( NTP4VCResult A B C D )
) $.

${
  $d w n A B C D $.

  $( Source declarations: D=char, A=power, B=a, and C=b. $)

  ntp4vc-character-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-power-function $e |- A e.
    ( ( Word D ) ^m ( ( Word D ) X. ZZ ) ) $.

  ntp4vc-power-recursion $e |- A. w e. Word D A. n e. ZZ
    (
      0 <_ n
      ->
      (
        (
          n = 0
          ->
          ( NTP4VCPower A w n ) = (/)
        )
        /\
        (
          n =/= 0
          ->
          ( NTP4VCPower A w n )
            = ( w ++ ( NTP4VCPower A w ( n - 1 ) ) )
        )
      )
    ) $.

  ntp4vc-a-word $e |- B e. Word D $.
  ntp4vc-b-word $e |- C e. Word D $.
  ntp4vc-commuting-words $e |- ( B ++ C ) = ( C ++ B ) $.

  ntp4vc-pearl-word-common-factor-top-common-factor-vc
    $a |- ( NTP4VCMain A B C D ) $.
$}
