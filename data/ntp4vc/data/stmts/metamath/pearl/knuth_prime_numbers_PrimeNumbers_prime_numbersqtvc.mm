$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/knuth_prime_numbers_PrimeNumbers_prime_numbersqtvc: the Knuth
  prime-number enumeration verification condition initializes the first two
  primes, searches successive odd candidates, and preserves the first-primes
  invariant through list updates. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and Word ZZ is the type of
  arbitrary finite zero-based integer sequences. NTP4VCToNat and NTP4VCSet
  reproduce Int.toNat and List.set. NTP4VCAt returns the source default zero
  at negative or out-of-range indices. NTP4VCUpdateLaw is the source
  extensional function-update
  equality. Prime is SetMM's set of positive integer primes, and the modulo-2
  tests are exactly integer oddness on every candidate admitted by the VC.

  NTP4VCTDiv is signed integer division truncated toward zero when its divisor
  is positive, as every divisor at its use sites is forced to be by
  first_primes. NTP4VCTMod is the associated signed remainder. The remaining
  predicates are biconditional definitions which only factor the source's
  nested quantifiers, implications, list updates, let bindings, and
  proposition-valued conditionals. Expanding them recovers the complete VC.

  The pinned original Why3 source tests mod n p[k] = 0 in the divisibility
  branch and then tests div n p[k] > p[k] in the square-bound branch. Thus
  this encoding uses NTP4VCTMod first and NTP4VCTDiv second, exactly in that
  source order. Lean 4 and Isabelle corroborate this reading; the secondary
  Rocq export swaps quotient and remainder and therefore does not override
  the original goal. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no artifact-level $p proof
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCTDiv NTP4VCTMod
  NTP4VCNoPrimeIn NTP4VCFirstPrimes NTP4VCZeros
  NTP4VCUpdateLaw NTP4VCCandidate NTP4VCNotDivBefore
  NTP4VCPrimeNext NTP4VCKOutcome NTP4VCKLoop
  NTP4VCJStep NTP4VCJLoop NTP4VCFinish
  NTP4VCOuter NTP4VCAfterSeeds
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-tdiv-syntax $a class ( NTP4VCTDiv A B ) $.
ntp4vc-tmod-syntax $a class ( NTP4VCTMod A B ) $.

ntp4vc-no-prime-in-syntax
  $a wff ( NTP4VCNoPrimeIn A B ) $.
ntp4vc-first-primes-syntax
  $a wff ( NTP4VCFirstPrimes A B ) $.
ntp4vc-zeros-syntax
  $a wff ( NTP4VCZeros A B ) $.
ntp4vc-update-law-syntax
  $a wff ( NTP4VCUpdateLaw A B C ) $.
ntp4vc-candidate-syntax
  $a wff ( NTP4VCCandidate A B C ) $.
ntp4vc-not-div-before-syntax
  $a wff ( NTP4VCNotDivBefore A B C ) $.
ntp4vc-prime-next-syntax
  $a wff ( NTP4VCPrimeNext A B C ) $.
ntp4vc-k-outcome-syntax
  $a wff ( NTP4VCKOutcome A B C D ) $.
ntp4vc-k-loop-syntax
  $a wff ( NTP4VCKLoop A B C ) $.
ntp4vc-j-step-syntax
  $a wff ( NTP4VCJStep A B C ) $.
ntp4vc-j-loop-syntax
  $a wff ( NTP4VCJLoop A B C ) $.
ntp4vc-finish-syntax
  $a wff ( NTP4VCFinish A B C D ) $.
ntp4vc-outer-syntax
  $a wff ( NTP4VCOuter A B ) $.
ntp4vc-after-seeds-syntax
  $a wff ( NTP4VCAfterSeeds A B ) $.

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
  (
    0 <_ B
    /\
    ( NTP4VCToNat B ) < ( # ` A )
  ) ,
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

ntp4vc-tdiv-definition $a |- (
  NTP4VCTDiv A B
) = if (
  A < 0 ,
  ( |^ ` ( A / B ) ) ,
  ( |_ ` ( A / B ) )
) $.

ntp4vc-tmod-definition $a |- (
  NTP4VCTMod A B
) = (
  A - ( B x. ( NTP4VCTDiv A B ) )
) $.

${
  $d x A B $.

  ntp4vc-no-prime-in-definition $a |- (
    ( NTP4VCNoPrimeIn A B )
    <->
    A. x e. ZZ
      (
        (
          A < x
          /\
          x < B
        )
        ->
        -. x e. Prime
      )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-first-primes-definition $a |- (
    ( NTP4VCFirstPrimes A B )
    <->
    (
      ( NTP4VCAt A 0 ) = 2
      /\
      (
        A. i e. ZZ A. j e. ZZ
          (
            (
              0 <_ i
              /\
              (
                i < j
                /\
                j < B
              )
            )
            ->
            ( NTP4VCAt A i ) < ( NTP4VCAt A j )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < B
              )
              ->
              ( NTP4VCAt A i ) e. Prime
            )
          /\
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < ( B - 1 )
              )
              ->
              (
                NTP4VCNoPrimeIn
                  ( NTP4VCAt A i )
                  ( NTP4VCAt A ( i + 1 ) )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-zeros-definition $a |- (
    ( NTP4VCZeros A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAt A i ) = 0
      )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-update-law-definition $a |- (
    ( NTP4VCUpdateLaw A B C )
    <->
    A. i e. ZZ
      (
        ( NTP4VCAt ( NTP4VCSet A B C ) i )
        =
        if (
          i = B ,
          C ,
          ( NTP4VCAt A i )
        )
      )
  ) $.
$}

ntp4vc-candidate-definition $a |- (
  ( NTP4VCCandidate A B C )
  <->
  (
    ( NTP4VCAt A ( B - 1 ) ) < C
    /\
    (
      C < ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
      /\
      (
        ( C mod 2 ) = 1
        /\
        (
          NTP4VCNoPrimeIn
            ( NTP4VCAt A ( B - 1 ) )
            C
        )
      )
    )
  )
) $.

${
  $d i A B C $.

  ntp4vc-not-div-before-definition $a |- (
    ( NTP4VCNotDivBefore A B C )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < C
        )
        ->
        -. ( ( NTP4VCAt A i ) || B )
      )
  ) $.
$}

ntp4vc-prime-next-definition $a |- (
  ( NTP4VCPrimeNext A B C )
  <->
  (
    ( NTP4VCAt A ( B - 1 ) ) < C
    /\
    (
      C e. Prime
      /\
      (
        NTP4VCNoPrimeIn
          ( NTP4VCAt A ( B - 1 ) )
          C
      )
    )
  )
) $.

ntp4vc-k-outcome-definition $a |- (
  ( NTP4VCKOutcome A B C D )
  <->
  (
    (
      0 <_ D
      /\
      D < ( # ` A )
    )
    /\
    (
      ( NTP4VCAt A D ) =/= 0
      /\
      (
        (
          ( NTP4VCTMod C ( NTP4VCAt A D ) ) = 0
          /\
          (
            (
              (
                (
                  0
                  <_
                  (
                    ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                    -
                    C
                  )
                  /\
                  (
                    ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                    -
                    ( C + 2 )
                  )
                  <
                  (
                    ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                    -
                    C
                  )
                )
                \/
                (
                  (
                    ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                    -
                    C
                  )
                  =
                  (
                    ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                    -
                    ( C + 2 )
                  )
                  /\
                  (
                    0 <_ ( B - D )
                    /\
                    ( B - 1 ) < ( B - D )
                  )
                )
              )
              /\
              (
                1 <_ 1
                /\
                1 < B
              )
            )
            /\
            (
              ( NTP4VCFirstPrimes A B )
              /\
              (
                ( NTP4VCCandidate A B ( C + 2 ) )
                /\
                ( NTP4VCNotDivBefore A ( C + 2 ) 1 )
              )
            )
          )
        )
        \/
        (
          ( NTP4VCTMod C ( NTP4VCAt A D ) ) =/= 0
          /\
          (
            (
              0 <_ D
              /\
              D < ( # ` A )
            )
            /\
            (
              (
                0 <_ D
                /\
                D < ( # ` A )
              )
              /\
              (
                ( NTP4VCAt A D ) =/= 0
                /\
                (
                  (
                    ( NTP4VCAt A D )
                    <
                    ( NTP4VCTDiv C ( NTP4VCAt A D ) )
                    /\
                    (
                      (
                        (
                          0
                          <_
                          (
                            ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                            -
                            C
                          )
                          /\
                          (
                            ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                            -
                            C
                          )
                          <
                          (
                            ( 2 x. ( NTP4VCAt A ( B - 1 ) ) )
                            -
                            C
                          )
                        )
                        \/
                        (
                          0 <_ ( B - D )
                          /\
                          ( B - ( D + 1 ) ) < ( B - D )
                        )
                      )
                      /\
                      (
                        1 <_ ( D + 1 )
                        /\
                        ( D + 1 ) < B
                      )
                    )
                    /\
                    (
                      ( NTP4VCFirstPrimes A B )
                      /\
                      (
                        ( NTP4VCCandidate A B C )
                        /\
                        ( NTP4VCNotDivBefore A C ( D + 1 ) )
                      )
                    )
                  )
                  \/
                  (
                    -.
                      ( NTP4VCAt A D )
                      <
                      ( NTP4VCTDiv C ( NTP4VCAt A D ) )
                    /\
                    ( NTP4VCPrimeNext A B C )
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
  $d k A B C $.

  ntp4vc-k-loop-definition $a |- (
    ( NTP4VCKLoop A B C )
    <->
    A. k e. ZZ
      (
        (
          (
            1 <_ k
            /\
            k < B
          )
          /\
          (
            ( NTP4VCFirstPrimes A B )
            /\
            (
              ( NTP4VCCandidate A B C )
              /\
              ( NTP4VCNotDivBefore A C k )
            )
          )
        )
        ->
        ( NTP4VCKOutcome A B C k )
      )
  ) $.
$}

${
  $d n p i A B C $.

  ntp4vc-j-step-definition $a |- (
    ( NTP4VCJStep A B C )
    <->
    (
      A. n e. ZZ A. p e. ( Word ZZ )
        (
          ( # ` p ) = ( # ` A )
          ->
          ( NTP4VCKLoop p B n )
        )
      /\
      (
        (
          (
            1 <_ 1
            /\
            1 < B
          )
          /\
          (
            ( NTP4VCFirstPrimes A B )
            /\
            ( NTP4VCCandidate A B C )
          )
        )
        /\
        ( NTP4VCNotDivBefore A C 1 )
      )
      /\
      A. n e. ZZ
        (
          ( NTP4VCPrimeNext A B n )
          ->
          (
            (
              0 <_ B
              /\
              B < ( # ` A )
            )
            /\
            (
              (
                # ` ( NTP4VCSet A B n )
              ) = ( # ` A )
              ->
              (
                ( NTP4VCUpdateLaw A B n )
                ->
                (
                  (
                    NTP4VCFirstPrimes
                      ( NTP4VCSet A B n )
                      ( B + 1 )
                  )
                  /\
                  (
                    NTP4VCCandidate
                      ( NTP4VCSet A B n )
                      ( B + 1 )
                      ( n + 2 )
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
  $d j A B C $.

  ntp4vc-j-loop-definition $a |- (
    ( NTP4VCJLoop A B C )
    <->
    A. j e. ZZ
      (
        (
          (
            2 <_ j
            /\
            j <_ C
          )
          /\
          (
            ( NTP4VCFirstPrimes A j )
            /\
            ( NTP4VCCandidate A j B )
          )
        )
        ->
        ( NTP4VCJStep A j B )
      )
  ) $.
$}

ntp4vc-finish-definition $a |- (
  ( NTP4VCFinish A B C D )
  <->
  (
    (
      ( NTP4VCFirstPrimes A ( C + 1 ) )
      /\
      ( NTP4VCCandidate A ( C + 1 ) B )
    )
    ->
    (
      ( # ` A ) = D
      /\
      ( NTP4VCFirstPrimes A D )
    )
  )
) $.

${
  $d n p A B $.

  ntp4vc-outer-definition $a |- (
    ( NTP4VCOuter A B )
    <->
    A. n e. ZZ A. p e. ( Word ZZ )
      (
        ( # ` p ) = ( # ` A )
        ->
        (
          ( NTP4VCJLoop p n ( B - 1 ) )
          /\
          ( NTP4VCFinish p n ( B - 1 ) B )
        )
      )
  ) $.
$}

ntp4vc-after-seeds-definition $a |- (
  ( NTP4VCAfterSeeds A B )
  <->
  (
    (
      2 <_ ( ( B - 1 ) + 1 )
      ->
      (
        (
          ( NTP4VCFirstPrimes A 2 )
          /\
          ( NTP4VCCandidate A 2 5 )
        )
        /\
        ( NTP4VCOuter A B )
      )
    )
    /\
    (
      ( ( B - 1 ) + 1 ) < 2
      ->
      (
        ( # ` A ) = B
        /\
        ( NTP4VCFirstPrimes A B )
      )
    )
  )
) $.

${
  $d p q A $.

  $( The source-global Bertrand-postulate assumption. $)
  ntp4vc-bertrand-postulate $e |- A. q e. Prime
    -. ( NTP4VCNoPrimeIn q ( 2 x. q ) ) $.

  $( Source theorem parameter A=m and its explicit fact0. $)
  ntp4vc-m-integer $e |- A e. ZZ $.
  ntp4vc-fact0 $e |- 2 <_ A $.

  ntp4vc-pearl-knuth-prime-numbers-vc $a |- (
    0 <_ A
    /\
    A. p e. ( Word ZZ )
      (
        (
          ( NTP4VCZeros p A )
          /\
          ( # ` p ) = A
        )
        ->
        (
          (
            0 <_ 0
            /\
            0 < ( # ` p )
          )
          /\
          (
            (
              # ` ( NTP4VCSet p 0 2 )
            ) = ( # ` p )
            ->
            (
              ( NTP4VCUpdateLaw p 0 2 )
              ->
              (
                (
                  0 <_ 1
                  /\
                  1 < ( # ` ( NTP4VCSet p 0 2 ) )
                )
                /\
                (
                  (
                    # `
                    (
                      NTP4VCSet
                        ( NTP4VCSet p 0 2 )
                        1
                        3
                    )
                  ) = ( # ` ( NTP4VCSet p 0 2 ) )
                  ->
                  (
                    (
                      NTP4VCUpdateLaw
                        ( NTP4VCSet p 0 2 )
                        1
                        3
                    )
                    ->
                    (
                      NTP4VCAfterSeeds
                        (
                          NTP4VCSet
                            ( NTP4VCSet p 0 2 )
                            1
                            3
                        )
                        A
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
