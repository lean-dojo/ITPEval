$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc
  (ntp4vc__metamath__pearl/verifythis_2021_lexicographic_permutations_1_Top_to_seqqtvc):
  the loop verification condition for copying an integer array into a finite
  sequence by appending each entry while preserving length and pointwise
  indexed values through initialization, preservation, and exit. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is exactly the
  type of arbitrary finite zero-based integer sequences. NTP4VCToNat and
  NTP4VCAt reproduce the source integer-to-natural conversion and totalized
  sequence lookup. NTP4VCSnoc is the exact finite-word append operation.

  The pinned Why3 source invariant is pointwise:
    forall i. 0 <= i < length s -> s[i] = a[i].
  NTP4VCPrefixCopy preserves that invariant verbatim. The secondary Lean,
  Rocq, and Isabelle exports replace the right-hand index in several invariant
  occurrences by the current sequence length; this file follows the primary
  Why3 source rather than that proposition-changing export defect.

  NTP4VCSnocSpec retains the three postconditions made available after the
  source snoc call. NTP4VCInitial, NTP4VCStep, NTP4VCExit, and NTP4VCFinal
  factor the loop initialization, preservation, exit, and function
  postcondition without changing their quantifier scopes. NTP4VCToSeqVC keeps
  the generated split between the nonnegative loop range and the impossible
  negative-range branch.

  The source array parameter is the sole essential hypothesis. The loop state
  remains internally quantified over every finite integer sequence. Every
  auxiliary $a declaration is syntax or an explicit faithful definition. The
  final $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSnoc NTP4VCO1
  NTP4VCPrefixCopy NTP4VCSnocSpec NTP4VCInitial
  NTP4VCStep NTP4VCExit NTP4VCFinal NTP4VCToSeqVC
$.

ntp4vc-to-nat-syntax
  $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax
  $a class ( NTP4VCAt A B ) $.
ntp4vc-snoc-syntax
  $a class ( NTP4VCSnoc A B ) $.
ntp4vc-o1-syntax
  $a class ( NTP4VCO1 A ) $.

ntp4vc-prefix-copy-syntax
  $a wff ( NTP4VCPrefixCopy A B C ) $.
ntp4vc-snoc-spec-syntax
  $a wff ( NTP4VCSnocSpec A B C ) $.
ntp4vc-initial-syntax
  $a wff ( NTP4VCInitial A ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B ) $.
ntp4vc-exit-syntax
  $a wff ( NTP4VCExit A B ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B ) $.
ntp4vc-to-seq-vc-syntax
  $a wff ( NTP4VCToSeqVC A ) $.

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
  $d k A B $.

  ntp4vc-snoc-definition $a |- (
    NTP4VCSnoc A B
  ) = (
    k e. ( 0 ..^ ( ( # ` A ) + 1 ) ) |->
      if (
        k < ( # ` A ) ,
        ( A ` k ) ,
        B
      )
  ) $.
$}

ntp4vc-o1-definition $a |- (
  NTP4VCO1 A
) = ( ( # ` A ) - 1 ) $.

${
  $d i A B C $.

  ntp4vc-prefix-copy-definition $a |- (
    NTP4VCPrefixCopy A B C
  ) <->
  A. i e. ZZ
    (
      (
        0 <_ i
        /\
        i < C
      )
      ->
      ( NTP4VCAt A i ) = ( NTP4VCAt B i )
    ) $.
$}

${
  $d i A B C $.

  ntp4vc-snoc-spec-definition $a |- (
    NTP4VCSnocSpec A B C
  ) <->
  (
    ( # ` C ) = ( 1 + ( # ` A ) )
    /\
    (
      ( NTP4VCAt C ( # ` A ) ) = B
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          ( NTP4VCAt C i ) = ( NTP4VCAt A i )
        )
    )
  ) $.
$}

ntp4vc-initial-definition $a |- (
  NTP4VCInitial A
) <->
(
  ( # ` (/) ) = 0
  /\
  ( NTP4VCPrefixCopy (/) A 0 )
) $.

ntp4vc-final-definition $a |- (
  NTP4VCFinal A B
) <->
(
  ( # ` A ) = ( # ` B )
  /\
  ( NTP4VCPrefixCopy A B ( # ` A ) )
) $.

ntp4vc-step-definition $a |- (
  NTP4VCStep A B
) <->
(
  (
    (
      0 <_ ( # ` B )
      /\
      ( # ` B ) <_ ( NTP4VCO1 A )
    )
    /\
    ( NTP4VCPrefixCopy B A ( # ` B ) )
  )
  ->
  (
    (
      0 <_ ( # ` B )
      /\
      ( # ` B ) < ( # ` A )
    )
    /\
    (
      (
        NTP4VCSnocSpec
          B
          ( NTP4VCAt A ( # ` B ) )
          ( NTP4VCSnoc B ( NTP4VCAt A ( # ` B ) ) )
      )
      ->
      (
        (
          #
          `
          ( NTP4VCSnoc B ( NTP4VCAt A ( # ` B ) ) )
        )
        =
        ( ( # ` B ) + 1 )
        /\
        (
          NTP4VCPrefixCopy
            ( NTP4VCSnoc B ( NTP4VCAt A ( # ` B ) ) )
            A
            ( ( # ` B ) + 1 )
        )
      )
    )
  )
) $.

ntp4vc-exit-definition $a |- (
  NTP4VCExit A B
) <->
(
  (
    (
      ( # ` B ) = ( ( NTP4VCO1 A ) + 1 )
      /\
      (
        NTP4VCPrefixCopy
          B
          A
          ( ( NTP4VCO1 A ) + 1 )
      )
    )
    ->
    ( NTP4VCFinal B A )
  )
) $.

${
  $d s A $.

  ntp4vc-to-seq-vc-definition $a |- (
    NTP4VCToSeqVC A
  ) <->
  (
    (
      0 <_ ( ( NTP4VCO1 A ) + 1 )
      ->
      (
        ( NTP4VCInitial A )
        /\
        A. s e. Word ZZ
          (
            ( NTP4VCStep A s )
            /\
            ( NTP4VCExit A s )
          )
      )
    )
    /\
    (
      ( ( NTP4VCO1 A ) + 1 ) < 0
      ->
      ( NTP4VCFinal (/) A )
    )
  ) $.
$}

${
  $d i k s
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameter a, an arbitrary finite integer array. $)
  ntp4vc-a-word $e |- A e. Word ZZ $.

  ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-to-seq-vc
    $a |- ( NTP4VCToSeqVC A ) $.
$}
