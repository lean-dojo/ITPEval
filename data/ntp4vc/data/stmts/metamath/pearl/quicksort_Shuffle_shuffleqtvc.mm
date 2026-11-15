$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/quicksort_Shuffle_shuffleqtvc: the Knuth-shuffle loop verification
  condition requires every bounded array swap to preserve permutation of the
  original integer array. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer arrays are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of unbounded integers.
  NTP4VCToNat, NTP4VCAt, and NTP4VCSet reproduce the exported integer-to-
  natural conversion, totalized lookup with default zero, and length-
  preserving list update.

  NTP4VCPerm compares the occurrence count of every integer and is
  bidirectionally equivalent to finite-list permutation. NTP4VCExchange
  defines the post-state as the exact forward swap of the pre-state, with
  both replacement values read from the pre-state. This follows the primary
  Why3 ArraySwap semantics, including the identity case of equal indices,
  rather than the reversed equation in the secondary Lean helper.

  The remaining predicates only factor the original nested verification
  condition. Expanding their biconditional definitions recovers both source
  let bindings, every integer and integer-list quantifier, all length and
  index assumptions, the two outer implications, and each permutation
  conclusion. Every quantified domain remains arbitrary. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet
  NTP4VCPerm NTP4VCExchange
  NTP4VCExchangeResults NTP4VCIndexResult
  NTP4VCAllIndices NTP4VCAllStates NTP4VCShuffleVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax
  $a class ( NTP4VCSet A B C ) $.

ntp4vc-perm-syntax
  $a wff ( NTP4VCPerm A B ) $.
ntp4vc-exchange-syntax
  $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-exchange-results-syntax
  $a wff ( NTP4VCExchangeResults A B C D ) $.
ntp4vc-index-result-syntax
  $a wff ( NTP4VCIndexResult A B C ) $.
ntp4vc-all-indices-syntax
  $a wff ( NTP4VCAllIndices A B C ) $.
ntp4vc-all-states-syntax
  $a wff ( NTP4VCAllStates A B ) $.
ntp4vc-shuffle-vc-syntax
  $a wff ( NTP4VCShuffleVC A ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

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
  $d k v A B $.

  ntp4vc-perm-definition $a |- (
    ( NTP4VCPerm A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        ( # ` A ) = ( # ` B )
        /\
        A. v e. ZZ
          (
            (
              # `
              { k e. ( 0 ..^ ( # ` A ) ) | ( A ` k ) = v }
            )
            =
            (
              # `
              { k e. ( 0 ..^ ( # ` B ) ) | ( B ` k ) = v }
            )
          )
      )
    )
  ) $.
$}

ntp4vc-exchange-definition $a |- (
  ( NTP4VCExchange A B C D )
  <->
  B = (
    NTP4VCSet
      ( NTP4VCSet A C ( NTP4VCAt A D ) )
      D
      ( NTP4VCAt A C )
  )
) $.

${
  $d x A B C D $.

  $( A=original, B=current, C=index, D=random index, x=next. $)
  ntp4vc-exchange-results-definition $a |- (
    ( NTP4VCExchangeResults A B C D )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` B )
        ->
        (
          ( NTP4VCExchange B x C D )
          ->
          ( NTP4VCPerm A x )
        )
      )
  ) $.
$}

${
  $d j A B C $.

  $( A=original, B=current, C=index, j=random index. $)
  ntp4vc-index-result-definition $a |- (
    ( NTP4VCIndexResult A B C )
    <->
    (
      0 < ( C + 1 )
      /\
      A. j e. ZZ
        (
          (
            0 <_ j
            /\
            j < ( C + 1 )
          )
          ->
          (
            (
              (
                0 <_ C
                /\
                C < ( # ` B )
              )
              /\
              (
                0 <_ j
                /\
                j < ( # ` B )
              )
            )
            /\
            ( NTP4VCExchangeResults A B C j )
          )
        )
    )
  ) $.
$}

${
  $d i A B C $.

  $( A=original, B=current, C=final index, i=loop index. $)
  ntp4vc-all-indices-definition $a |- (
    ( NTP4VCAllIndices A B C )
    <->
    A. i e. ZZ
      (
        (
          (
            (
              1 <_ i
              /\
              i <_ C
            )
            /\
            ( NTP4VCPerm A B )
          )
          ->
          ( NTP4VCIndexResult A B i )
        )
      )
  ) $.
$}

${
  $d x A B $.

  $( A=original, B=final index, x=current. $)
  ntp4vc-all-states-definition $a |- (
    ( NTP4VCAllStates A B )
    <->
    A. x e. Word ZZ
      (
        ( # ` x ) = ( # ` A )
        ->
        ( NTP4VCAllIndices A x B )
      )
  ) $.
$}

ntp4vc-shuffle-vc-definition $a |- (
  ( NTP4VCShuffleVC A )
  <->
  (
    (
      1 <_ ( ( ( # ` A ) - 1 ) + 1 )
      ->
      (
        ( NTP4VCPerm A A )
        /\
        ( NTP4VCAllStates A ( ( # ` A ) - 1 ) )
      )
    )
    /\
    (
      ( ( ( # ` A ) - 1 ) + 1 ) < 1
      ->
      ( NTP4VCPerm A A )
    )
  )
) $.

${
  $( Source theorem parameter A=a. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.

  ntp4vc-pearl-quicksort-shuffle-shuffle-vc $a |- (
    NTP4VCShuffleVC A
  ) $.
$}
