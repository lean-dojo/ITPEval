$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sieve_Sieve_sieveqtvc: the sieve verification condition initializes a
  Boolean array, clears zero and one, preserves no-small-factor invariants
  while marking multiples, and concludes that exactly the prime indices are
  marked. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word {0, 1} is exactly
  the type of arbitrary finite zero-based Boolean sequences, with false
  encoded by 0 and true by 1. NTP4VCToNat is the exported integer-to-natural
  conversion, NTP4VCAt is integer-indexed lookup with default zero outside
  [0, length), and NTP4VCSet is list update. NTP4VCUpdateLaw is the exported
  extensional equality between lookup after update and integer-domain
  function update.

  NTP4VCNoFactorLt is the source predicate no_factor_lt. The remaining
  predicates are biconditional definitions that factor only the source
  conjunctions, quantifiers, implications, let-bound false values, and
  proposition-valued conditionals. Every conditional is represented by its
  two exhaustive guarded implications. Prime is SetMM's class of positive
  integer primes; under the source's nonnegative index guard it is equivalent
  to the Lean export's Nat.Prime after Int.toNat.

  Thus all integer and Boolean-sequence quantifiers retain their complete
  source domains, and expanding the definitions recovers the full sieve VC.
  The final $a declaration is Metamath's native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCUpdateLaw
  NTP4VCNoFactorLt NTP4VCInitialized
  NTP4VCOuterInv NTP4VCInnerInv NTP4VCFinal
  NTP4VCOuterAdvance NTP4VCInnerUpdate NTP4VCInnerResult
  NTP4VCCandidateTrue NTP4VCOuterBody NTP4VCOuterStep
  NTP4VCAfterTwo NTP4VCAfterOne NTP4VCStart
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.

ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C ) $.
ntp4vc-no-factor-lt-syntax
  $a wff ( NTP4VCNoFactorLt A B ) $.
ntp4vc-initialized-syntax
  $a wff ( NTP4VCInitialized A B ) $.
ntp4vc-outer-inv-syntax
  $a wff ( NTP4VCOuterInv A B C ) $.
ntp4vc-inner-inv-syntax
  $a wff ( NTP4VCInnerInv A B C D ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B ) $.
ntp4vc-outer-advance-syntax
  $a wff ( NTP4VCOuterAdvance A B C ) $.
ntp4vc-inner-update-syntax
  $a wff ( NTP4VCInnerUpdate A B C D ) $.
ntp4vc-inner-result-syntax
  $a wff ( NTP4VCInnerResult A B C D ) $.
ntp4vc-candidate-true-syntax
  $a wff ( NTP4VCCandidateTrue A B C ) $.
ntp4vc-outer-body-syntax
  $a wff ( NTP4VCOuterBody A B C ) $.
ntp4vc-outer-step-syntax
  $a wff ( NTP4VCOuterStep A B C ) $.
ntp4vc-after-two-syntax
  $a wff ( NTP4VCAfterTwo A B ) $.
ntp4vc-after-one-syntax
  $a wff ( NTP4VCAfterOne A B ) $.
ntp4vc-start-syntax
  $a wff ( NTP4VCStart A B ) $.

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
  ( 0 <_ B /\ B < ( # ` A ) ) ,
  ( A ` B ) ,
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
  $d k A B C $.

  ntp4vc-update-law-definition $a |- (
    NTP4VCUpdateLaw A B C
  ) <-> (
    A. k e. ZZ
      (
        NTP4VCAt ( NTP4VCSet A B C ) k
      ) = if (
        k = B ,
        C ,
        ( NTP4VCAt A k )
      )
  ) $.
$}

${
  $d k l A B $.

  ntp4vc-no-factor-lt-definition $a |- (
    NTP4VCNoFactorLt A B
  ) <-> (
    1 < B
    /\
    A. k e. ZZ A. l e. ZZ
      (
        (
          (
            1 < l
            /\
            l < A
          )
          /\
          1 < k
        )
        ->
        B =/= ( k x. l )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-initialized-definition $a |- (
    NTP4VCInitialized A B
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAt A i ) = 1
      )
    /\
    ( # ` A ) = B
  ) $.
$}

${
  $d j A B C $.

  ntp4vc-outer-inv-definition $a |- (
    NTP4VCOuterInv A B C
  ) <-> (
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < C
        )
        ->
        (
          ( NTP4VCAt A j ) = 1
          <->
          ( NTP4VCNoFactorLt B j )
        )
      )
  ) $.
$}

${
  $d j k A B C D $.

  ntp4vc-inner-inv-definition $a |- (
    NTP4VCInnerInv A B C D
  ) <-> (
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < D
        )
        ->
        (
          ( NTP4VCAt A j ) = 1
          <->
          (
            ( NTP4VCNoFactorLt B j )
            /\
            A. k e. ZZ
              (
                (
                  1 < k
                  /\
                  k < C
                )
                ->
                j =/= ( k x. B )
              )
          )
        )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-final-definition $a |- (
    NTP4VCFinal A B
  ) <-> (
    ( # ` A ) = B
    /\
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          ( NTP4VCAt A i ) = 1
          <->
          i e. Prime
        )
      )
  ) $.
$}

ntp4vc-outer-advance-definition $a |- (
  NTP4VCOuterAdvance A B C
) <-> (
  (
    0 <_ ( C - B )
    /\
    ( C - ( B + 1 ) ) < ( C - B )
  )
  /\
  (
    (
      1 < ( B + 1 )
      /\
      ( B + 1 ) <_ C
    )
    /\
    ( NTP4VCOuterInv A ( B + 1 ) C )
  )
) $.

ntp4vc-inner-update-definition $a |- (
  NTP4VCInnerUpdate A B C D
) <-> (
  (
    0 <_ ( C x. B )
    /\
    ( C x. B ) < ( # ` A )
  )
  /\
  (
    (
      # ` ( NTP4VCSet A ( C x. B ) 0 )
    ) = ( # ` A )
    ->
    (
      ( NTP4VCUpdateLaw A ( C x. B ) 0 )
      ->
      (
        (
          0 <_ ( D - C )
          /\
          ( D - ( C + 1 ) ) < ( D - C )
        )
        /\
        (
          (
            (
              1 < ( C + 1 )
              /\
              ( C + 1 ) <_ D
            )
            /\
            (
              ( ( C x. B ) + B )
              =
              ( ( C + 1 ) x. B )
            )
          )
          /\
          (
            NTP4VCInnerInv
              ( NTP4VCSet A ( C x. B ) 0 )
              B
              ( C + 1 )
              D
          )
        )
      )
    )
  )
) $.

ntp4vc-inner-result-definition $a |- (
  NTP4VCInnerResult A B C D
) <-> (
  (
    ( C x. B ) < D
    ->
    ( NTP4VCInnerUpdate A B C D )
  )
  /\
  (
    -. ( C x. B ) < D
    ->
    ( NTP4VCOuterAdvance A B D )
  )
) $.

${
  $d r t A B C $.

  ntp4vc-candidate-true-definition $a |- (
    NTP4VCCandidateTrue A B C
  ) <-> (
    (
      (
        1 < B
        /\
        B <_ C
      )
      /\
      ( NTP4VCInnerInv A B B C )
    )
    /\
    A. r e. ZZ A. t e. ( Word { 0 , 1 } )
      (
        ( # ` t ) = ( # ` A )
        ->
        (
          (
            (
              1 < r
              /\
              r <_ C
            )
            /\
            ( NTP4VCInnerInv t B r C )
          )
          ->
          ( NTP4VCInnerResult t B r C )
        )
      )
  ) $.
$}

ntp4vc-outer-body-definition $a |- (
  NTP4VCOuterBody A B C
) <-> (
  (
    0 <_ B
    /\
    B < ( # ` A )
  )
  /\
  (
    (
      ( NTP4VCAt A B ) = 1
      ->
      ( NTP4VCCandidateTrue A B C )
    )
    /\
    (
      -. ( NTP4VCAt A B ) = 1
      ->
      ( NTP4VCOuterAdvance A B C )
    )
  )
) $.

ntp4vc-outer-step-definition $a |- (
  NTP4VCOuterStep A B C
) <-> (
  (
    B < C
    ->
    ( NTP4VCOuterBody A B C )
  )
  /\
  (
    -. B < C
    ->
    ( NTP4VCFinal A C )
  )
) $.

${
  $d i t A B $.

  ntp4vc-after-two-definition $a |- (
    NTP4VCAfterTwo A B
  ) <-> (
    (
      (
        1 < 2
        /\
        2 <_ B
      )
      /\
      ( NTP4VCOuterInv A 2 B )
    )
    /\
    A. i e. ZZ A. t e. ( Word { 0 , 1 } )
      (
        ( # ` t ) = ( # ` A )
        ->
        (
          (
            (
              1 < i
              /\
              i <_ B
            )
            /\
            ( NTP4VCOuterInv t i B )
          )
          ->
          ( NTP4VCOuterStep t i B )
        )
      )
  ) $.
$}

ntp4vc-after-one-definition $a |- (
  NTP4VCAfterOne A B
) <-> (
  (
    0 <_ 1
    /\
    1 < ( # ` A )
  )
  /\
  (
    (
      # ` ( NTP4VCSet A 1 0 )
    ) = ( # ` A )
    ->
    (
      ( NTP4VCUpdateLaw A 1 0 )
      ->
      (
        NTP4VCAfterTwo
          ( NTP4VCSet A 1 0 )
          B
      )
    )
  )
) $.

ntp4vc-start-definition $a |- (
  NTP4VCStart A B
) <-> (
  (
    0 <_ 0
    /\
    0 < ( # ` A )
  )
  /\
  (
    (
      # ` ( NTP4VCSet A 0 0 )
    ) = ( # ` A )
    ->
    (
      ( NTP4VCUpdateLaw A 0 0 )
      ->
      (
        NTP4VCAfterOne
          ( NTP4VCSet A 0 0 )
          B
      )
    )
  )
) $.

${
  $d t
     A B C D E F G H I J K L M N O P Q R S T U V W X Y Z $.

  $( Source theorem parameter A=n and its explicit precondition. $)
  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-fact0 $e |- 1 < A $.

  ntp4vc-pearl-sieve-vc $a |- (
    0 <_ A
    /\
    A. t e. ( Word { 0 , 1 } )
      (
        ( NTP4VCInitialized t A )
        ->
        ( NTP4VCStart t A )
      )
  ) $.
$}
