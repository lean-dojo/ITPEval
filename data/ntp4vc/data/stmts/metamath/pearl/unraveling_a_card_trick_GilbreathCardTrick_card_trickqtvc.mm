$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc
  (ntp4vc__metamath__pearl/unraveling_a_card_trick_GilbreathCardTrick_card_trickqtvc):
  the Gilbreath card-trick verification condition for cutting an ordered
  finite deck into stacks, reversing the cut stack, and riffle-shuffling the
  two parts to obtain suit-sorted blocks. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  source type of arbitrary finite zero-based integer lists. A Why3 Stack.t int
  has only its mutable elts list as mathematical data, while Stack.length is
  the length of that list, so stacks are represented extensionally and
  bijectively by Word ZZ.

  NTP4VCReverse is exact finite-list reversal. NTP4VCShuffle is the least
  ternary relation on integer words containing the two empty-side cases and
  closed under taking the next card from either input; this is exactly the
  four-constructor source inductive predicate. NTP4VCSuitOrdered and
  NTP4VCSuitSorted expand the two Why3 predicates over the full integer
  domain. Word application outside its finite index domain cannot equal an
  integer, matching Why3 nth returning None rather than Some v.

  The source theory assumptions m_positive, n_nonnegative, and
  gilbreath_card_trick are scoped essential hypotheses. Every loop state,
  match witness, successor stack, shuffle result, cut, and nondeterministic
  integer result remains quantified at its source scope. The nonempty-list
  match is equivalently written as exact singleton-cons decomposition.

  Expanding the definitions gives the original Why3 verification condition
  and the agreeing Lean, Rocq, and Isabelle exports. Every auxiliary $a below
  is syntax or a faithful definitional abbreviation. The final $a declaration
  is Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCReverse NTP4VCShuffle NTP4VCSuitOrdered NTP4VCSuitSorted
  NTP4VCInvariant NTP4VCStep NTP4VCFinish NTP4VCInitial
  NTP4VCPositiveCut NTP4VCNegativeCut NTP4VCCardTrickVC
$.

$v j2 a1 a2 d2 o1 result cut $.
ntp4vc-j2-setvar $f setvar j2 $.
ntp4vc-a1-setvar $f setvar a1 $.
ntp4vc-a2-setvar $f setvar a2 $.
ntp4vc-d2-setvar $f setvar d2 $.
ntp4vc-o1-setvar $f setvar o1 $.
ntp4vc-result-setvar $f setvar result $.
ntp4vc-cut-setvar $f setvar cut $.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-shuffle-syntax
  $a wff ( NTP4VCShuffle A B C ) $.
ntp4vc-suit-ordered-syntax
  $a wff ( NTP4VCSuitOrdered A B C ) $.
ntp4vc-suit-sorted-syntax
  $a wff ( NTP4VCSuitSorted A B C ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C D E ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A B C D ) $.
ntp4vc-positive-cut-syntax
  $a wff ( NTP4VCPositiveCut A B C D E ) $.
ntp4vc-negative-cut-syntax
  $a wff ( NTP4VCNegativeCut A B C D ) $.
ntp4vc-card-trick-vc-syntax
  $a wff ( NTP4VCCardTrickVC A B C D ) $.

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d a b c l x A B C R $.

  ntp4vc-shuffle-definition $a |- (
    NTP4VCShuffle A B C
  ) <-> (
    A. R
      (
        (
          (
            A. l e. Word ZZ
              <. <. l , (/) >. , l >. e. R
            /\
            A. l e. Word ZZ
              <. <. (/) , l >. , l >. e. R
          )
          /\
          (
            A. x e. ZZ
              A. a e. Word ZZ A. b e. Word ZZ A. c e. Word ZZ
                (
                  <. <. a , b >. , c >. e. R
                  ->
                  <.
                    <. ( <" x "> ++ a ) , b >. ,
                    ( <" x "> ++ c )
                  >. e. R
                )
            /\
            A. x e. ZZ
              A. a e. Word ZZ A. b e. Word ZZ A. c e. Word ZZ
                (
                  <. <. a , b >. , c >. e. R
                  ->
                  <.
                    <. a , ( <" x "> ++ b ) >. ,
                    ( <" x "> ++ c )
                  >. e. R
                )
          )
        )
        ->
        <. <. A , B >. , C >. e. R
      )
  ) $.
$}

${
  $d i j A N M $.

  ntp4vc-suit-ordered-definition $a |- (
    NTP4VCSuitOrdered A N M
  ) <-> (
    A. i e. ZZ A. j e. ZZ
      (
        (
          0 <_ i
          /\
          i < N
        )
        ->
        (
          (
            0 <_ j
            /\
            j < M
          )
          ->
          ( A ` ( ( i x. M ) + j ) ) = j
        )
      )
  ) $.
$}

${
  $d i j1 j2 v A N M $.

  ntp4vc-suit-sorted-definition $a |- (
    NTP4VCSuitSorted A N M
  ) <-> (
    (
      A. i e. ZZ A. v e. ZZ
        (
          ( A ` i ) = v
          ->
          (
            0 <_ v
            /\
            v < M
          )
        )
    )
    /\
    A. i e. ZZ A. j1 e. ZZ A. j2 e. ZZ
      (
        (
          0 <_ i
          /\
          i < N
        )
        ->
        (
          (
            0 <_ j1
            /\
            j1 < M
          )
          ->
          (
            (
              0 <_ j2
              /\
              j2 < M
            )
            ->
            ( A ` ( ( i x. M ) + j1 ) )
            =/=
            ( A ` ( ( i x. M ) + j2 ) )
          )
        )
      )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  NTP4VCInvariant A B C I N M
) <-> (
  ( # ` C ) = ( ( ( N x. M ) - I ) + 1 )
  /\
  (
    ( # ` B ) = ( I - 1 )
    /\
    A = ( ( NTP4VCReverse B ) ++ C )
  )
) $.

${
  $d a2 d2 o1 A B C I N M $.

  ntp4vc-step-definition $a |- (
    NTP4VCStep A B C I N M
  ) <-> (
    C =/= (/)
    /\
    A. a2 e. Word ZZ A. o1 e. ZZ
      (
        C = ( <" o1 "> ++ a2 )
        ->
        A. d2 e. Word ZZ
          (
            d2 = ( <" o1 "> ++ B )
            ->
            ( NTP4VCInvariant A d2 a2 ( I + 1 ) N M )
          )
      )
  ) $.
$}

${
  $d a2 d2 result A B C N M $.

  ntp4vc-finish-definition $a |- (
    NTP4VCFinish A B C N M
  ) <-> (
    A. d2 e. Word ZZ A. a2 e. Word ZZ A. result e. Word ZZ
      (
        (
          a2 = (/)
          /\
          (
            d2 = (/)
            /\
            (
              NTP4VCShuffle
                ( NTP4VCReverse C )
                ( NTP4VCReverse B )
                result
            )
          )
        )
        ->
        (
          ( # ` result ) = ( N x. M )
          /\
          ( NTP4VCSuitSorted result N M )
        )
      )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A B N M
) <-> (
  ( # ` A ) = ( ( ( N x. M ) - 1 ) + 1 )
  /\
  (
    ( # ` B ) = ( 1 - 1 )
    /\
    A = ( ( NTP4VCReverse B ) ++ A )
  )
) $.

${
  $d a1 d1 i A B C N M $.

  ntp4vc-positive-cut-definition $a |- (
    NTP4VCPositiveCut A B C N M
  ) <-> (
    ( NTP4VCInitial A B N M )
    /\
    A. d1 e. Word ZZ A. a1 e. Word ZZ
      (
        (
          A. i e. ZZ
            (
              (
                (
                  1 <_ i
                  /\
                  i <_ C
                )
                /\
                ( NTP4VCInvariant A d1 a1 i N M )
              )
              ->
              ( NTP4VCStep A d1 a1 i N M )
            )
        )
        /\
        (
          ( NTP4VCInvariant A d1 a1 ( C + 1 ) N M )
          ->
          ( NTP4VCFinish A d1 a1 N M )
        )
      )
  ) $.
$}

${
  $d a1 d1 result A B N M $.

  ntp4vc-negative-cut-definition $a |- (
    NTP4VCNegativeCut A B N M
  ) <-> (
    A. d1 e. Word ZZ A. a1 e. Word ZZ A. result e. Word ZZ
      (
        (
          a1 = (/)
          /\
          (
            d1 = (/)
            /\
            (
              NTP4VCShuffle
                ( NTP4VCReverse A )
                ( NTP4VCReverse B )
                result
            )
          )
        )
        ->
        (
          ( # ` result ) = ( N x. M )
          /\
          ( NTP4VCSuitSorted result N M )
        )
      )
  ) $.
$}

${
  $d cut result A B N M $.

  ntp4vc-card-trick-vc-definition $a |- (
    NTP4VCCardTrickVC A B N M
  ) <-> (
    (
      E. result e. ZZ
        (
          0 <_ result
          /\
          result <_ ( N x. M )
        )
    )
    /\
    A. cut e. ZZ
      (
        (
          0 <_ cut
          /\
          cut <_ ( N x. M )
        )
        ->
        (
          (
            1 <_ ( cut + 1 )
            ->
            ( NTP4VCPositiveCut A B cut N M )
          )
          /\
          (
            ( cut + 1 ) < 1
            ->
            ( NTP4VCNegativeCut A B N M )
          )
        )
      )
  ) $.
$}

${
  $d a b c d
     a1 a2 d1 d2 i j j1 j2 l o1 result v x
     A B C D M N R $.

  $( Source constants m and n and their theory assumptions. $)
  ntp4vc-m-integer $e |- M e. ZZ $.
  ntp4vc-n-integer $e |- N e. ZZ $.
  ntp4vc-m-positive $e |- 0 < M $.
  ntp4vc-n-nonnegative $e |- 0 <_ N $.

  $(
    Source theory axiom gilbreath_card_trick, with the exact ordered-deck,
    cut, reversed-cut shuffle, and suit-sorted conclusion.
  $)
  ntp4vc-gilbreath-card-trick $e |-
    A. a e. Word ZZ A. c e. Word ZZ A. d e. Word ZZ
      A. b e. Word ZZ
        (
          ( # ` a ) = ( N x. M )
          ->
          (
            ( NTP4VCSuitOrdered a N M )
            ->
            (
              a = ( c ++ d )
              ->
              (
                ( NTP4VCShuffle c ( NTP4VCReverse d ) b )
                ->
                ( NTP4VCSuitSorted b N M )
              )
            )
          )
        ) $.

  $( Source theorem parameters a and d', followed by fact0--fact2. $)
  ntp4vc-a-stack $e |- A e. Word ZZ $.
  ntp4vc-d-prime-stack $e |- B e. Word ZZ $.
  ntp4vc-fact0 $e |- ( # ` A ) = ( N x. M ) $.
  ntp4vc-fact1 $e |- ( NTP4VCSuitOrdered A N M ) $.
  ntp4vc-fact2 $e |- B = (/) $.

  ntp4vc-pearl-unraveling-a-card-trick-gilbreath-card-trick-card-trick-vc
    $a |- ( NTP4VCCardTrickVC A B N M ) $.
$}
