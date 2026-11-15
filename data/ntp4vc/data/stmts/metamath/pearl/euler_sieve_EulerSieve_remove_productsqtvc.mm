$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieve_remove_productsqtvc: the Euler-sieve
  remove-products verification condition marks odd prime multiples, advances
  the linked next-index structure, preserves the sieve invariants, and
  establishes the next outer-loop state. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  S is the arbitrary nonempty sieve-state carrier. N, M, and X are the
  source nexts, marked, and signed-63-bit max accessors. Signed 63-bit words
  are represented exactly by the integer interval [-2^62,2^62), integer and
  Boolean lists by arbitrary finite SetMM words over ZZ and 2, and list
  lookup is totalized with the source defaults after Int.toNat.

  NTP4VCSet is the exact source List.set operation. NTP4VCTDiv is signed
  integer division truncated toward zero; the divisor in this VC is positive.
  The named sieve predicates are biconditional definitions of the source
  specifications. The transition predicates only factor the nested
  quantifiers, implications, list updates, and proposition-valued conditionals:
  expanding them recovers the complete verification condition.

  The Lean and Isabelle sources render the bound d as the quotient max/n,
  which is also the algorithmic quantity used by the subsequent comparison;
  this encoding follows that common quotient reading. The final declaration
  is Metamath's native unproved $a statement encoding. There is no $p proof
  declaration in this database.
$)

$c
  NTP4VCIn63 NTP4VCBV63 NTP4VCToNat
  NTP4VCAtInt NTP4VCAtBool NTP4VCSet NTP4VCTDiv
  NTP4VCInvNexts NTP4VCAllEliminated NTP4VCStateInv
  NTP4VCAllPrimes NTP4VCAllMultiples NTP4VCPreviously
  NTP4VCOnly NTP4VCPrimeMarked NTP4VCInvRemove
  NTP4VCNotNext NTP4VCIsCopy NTP4VCAllElimPartial
  NTP4VCNotNextPartial NTP4VCLoopInv NTP4VCExit
  NTP4VCFinalPost NTP4VCFinalize NTP4VCUnmarkedStep
  NTP4VCMarkedAdvance NTP4VCMarkedCase NTP4VCAfterMark
  NTP4VCBoolStep NTP4VCScanStep NTP4VCNextStep
  NTP4VCLoopBody NTP4VCMainLoop NTP4VCSquareStep
$.

ntp4vc-in63-syntax $a wff ( NTP4VCIn63 A ) $.
ntp4vc-bv63-syntax $a class NTP4VCBV63 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-int-syntax $a class ( NTP4VCAtInt A B ) $.
ntp4vc-at-bool-syntax $a class ( NTP4VCAtBool A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-tdiv-syntax $a class ( NTP4VCTDiv A B ) $.

ntp4vc-inv-nexts-syntax
  $a wff ( NTP4VCInvNexts A B ) $.
ntp4vc-all-eliminated-syntax
  $a wff ( NTP4VCAllEliminated A B ) $.
ntp4vc-state-inv-syntax
  $a wff ( NTP4VCStateInv A B C ) $.
ntp4vc-all-primes-syntax
  $a wff ( NTP4VCAllPrimes A B ) $.
ntp4vc-all-multiples-syntax
  $a wff ( NTP4VCAllMultiples A B C ) $.
ntp4vc-previously-syntax
  $a wff ( NTP4VCPreviously A B ) $.
ntp4vc-only-syntax
  $a wff ( NTP4VCOnly A B ) $.
ntp4vc-prime-marked-syntax
  $a wff ( NTP4VCPrimeMarked A B C D ) $.
ntp4vc-inv-remove-syntax
  $a wff ( NTP4VCInvRemove A B C ) $.
ntp4vc-not-next-syntax
  $a wff ( NTP4VCNotNext A B C ) $.
ntp4vc-is-copy-syntax
  $a wff ( NTP4VCIsCopy A B ) $.
ntp4vc-all-elim-partial-syntax
  $a wff ( NTP4VCAllElimPartial A B C ) $.
ntp4vc-not-next-partial-syntax
  $a wff ( NTP4VCNotNextPartial A B C D ) $.
ntp4vc-loop-inv-syntax
  $a wff ( NTP4VCLoopInv A B C D E F G ) $.
ntp4vc-exit-syntax
  $a wff ( NTP4VCExit A B C D ) $.
ntp4vc-final-post-syntax
  $a wff ( NTP4VCFinalPost A B C ) $.
ntp4vc-finalize-syntax
  $a wff ( NTP4VCFinalize A B C D E F G ) $.
ntp4vc-unmarked-step-syntax
  $a wff ( NTP4VCUnmarkedStep A B C D E F G H ) $.
ntp4vc-marked-advance-syntax
  $a wff (
    NTP4VCMarkedAdvance A B C D E F G H I J K L
  ) $.
ntp4vc-marked-case-syntax
  $a wff ( NTP4VCMarkedCase A B C D E F G H I J K ) $.
ntp4vc-after-mark-syntax
  $a wff ( NTP4VCAfterMark A B C D E F G H I J K ) $.
ntp4vc-bool-step-syntax
  $a wff ( NTP4VCBoolStep A B C D E F G H I J K L ) $.
ntp4vc-scan-step-syntax
  $a wff ( NTP4VCScanStep A B C D E F G H I J K ) $.
ntp4vc-next-step-syntax
  $a wff ( NTP4VCNextStep A B C D E F G H I J ) $.
ntp4vc-loop-body-syntax
  $a wff ( NTP4VCLoopBody A B C D E F G H I J K ) $.
ntp4vc-main-loop-syntax
  $a wff ( NTP4VCMainLoop A B C D E F G H I ) $.
ntp4vc-square-step-syntax
  $a wff ( NTP4VCSquareStep A B C D E F G H ) $.

ntp4vc-in63-definition $a |- (
  ( NTP4VCIn63 A )
  <->
  (
    ( -u ( 2 ^ ; 6 2 ) ) <_ A
    /\
    A < ( 2 ^ ; 6 2 )
  )
) $.

ntp4vc-bv63-definition $a |- NTP4VCBV63 = {
  x e. ZZ | ( NTP4VCIn63 x )
} $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-int-definition $a |- (
  NTP4VCAtInt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-at-bool-definition $a |- (
  NTP4VCAtBool A B
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

ntp4vc-tdiv-definition $a |- (
  NTP4VCTDiv A B
) = if (
  A < 0 ,
  ( |^ ` ( A / B ) ) ,
  ( |_ ` ( A / B ) )
) $.

${
  $d i A B $.

  ntp4vc-inv-nexts-definition $a |- (
    ( NTP4VCInvNexts A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          i < ( NTP4VCAtInt A i )
          /\
          ( NTP4VCAtInt A i ) <_ B
        )
      )
  ) $.
$}

${
  $d i j A B $.

  ntp4vc-all-eliminated-definition $a |- (
    ( NTP4VCAllEliminated A B )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          A. j e. ZZ
            (
              (
                i < j
                /\
                j < ( NTP4VCAtInt B i )
              )
              ->
              ( NTP4VCAtBool A j ) = 1
            )
        )
    )
  ) $.
$}

${
  $d i A B C $.

  ntp4vc-state-inv-definition $a |- (
    ( NTP4VCStateInv A B C )
    <->
    (
      C < ( ( 2 ^ ; 6 2 ) - 1 )
      /\
      (
        3 <_ C
        /\
        (
          ( # ` A ) = ( # ` B )
          /\
          (
            ( # ` B ) = ( C + 1 )
            /\
            (
              ( NTP4VCInvNexts A ( # ` A ) )
              /\
              (
                ( NTP4VCAllEliminated B A )
                /\
                (
                  A. i e. ZZ
                    (
                      (
                        3 <_ i
                        /\
                        i <_ C
                      )
                      ->
                      (
                        ( i mod 2 ) = 0
                        ->
                        ( NTP4VCAtBool B i ) = 1
                      )
                    )
                  /\
                  (
                    A. i e. ZZ
                      (
                        (
                          3 <_ i
                          /\
                          i < ( C - 1 )
                        )
                        ->
                        (
                          ( i mod 2 ) = 1
                          ->
                          (
                            ( ( NTP4VCAtInt A i ) mod 2 ) = 1
                            \/
                            ( NTP4VCAtInt A i ) = ( C + 1 )
                          )
                        )
                      )
                    /\
                    (
                      ( NTP4VCAtInt A C ) = ( C + 1 )
                      /\
                      (
                        (
                          ( ( C - 1 ) mod 2 ) = 0
                          ->
                          ( NTP4VCAtInt A ( C - 1 ) ) = C
                        )
                        /\
                        (
                          ( ( C - 1 ) mod 2 ) = 1
                          ->
                          ( NTP4VCAtInt A ( C - 1 ) ) = ( C + 1 )
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
$}

${
  $d i A B $.

  ntp4vc-all-primes-definition $a |- (
    ( NTP4VCAllPrimes A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        (
          -. ( NTP4VCAtBool A i ) = 1
          <->
          i e. Prime
        )
      )
  ) $.
$}

${
  $d k A B C $.

  ntp4vc-all-multiples-definition $a |- (
    ( NTP4VCAllMultiples A B C )
    <->
    (
      (
        2 <_ B
        /\
        B < ( # ` A )
      )
      /\
      A. k e. ZZ
        (
          (
            2 <_ k
            /\
            k < C
          )
          ->
          (
            ( B x. k ) < ( # ` A )
            ->
            ( NTP4VCAtBool A ( B x. k ) ) = 1
          )
        )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-previously-definition $a |- (
    ( NTP4VCPreviously A B )
    <->
    A. i e. ZZ
      (
        (
          2 <_ i
          /\
          i < B
        )
        ->
        ( NTP4VCAllMultiples A i ( # ` A ) )
      )
  ) $.
$}

${
  $d i j k A B $.

  ntp4vc-only-definition $a |- (
    ( NTP4VCOnly A B )
    <->
    A. k e. ZZ
      (
        (
          2 <_ k
          /\
          k < ( # ` A )
        )
        ->
        (
          ( NTP4VCAtBool A k ) = 1
          ->
          E. i e. ZZ E. j e. ZZ
            (
              (
                2 <_ i
                /\
                i < B
              )
              /\
              (
                (
                  2 <_ j
                  /\
                  j < ( # ` A )
                )
                /\
                ( i x. j ) = k
              )
            )
        )
      )
  ) $.
$}

${
  $d i A B C D $.

  ntp4vc-prime-marked-definition $a |- (
    ( NTP4VCPrimeMarked A B C D )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        (
          C < D
          /\
          D <_ ( # ` B )
        )
        /\
        A. i e. ZZ
          (
            (
              C <_ i
              /\
              i < D
            )
            ->
            (
              -. ( NTP4VCAtBool A i ) = 1
              ->
              (
                ( C x. i ) < ( # ` A )
                ->
                ( NTP4VCAtBool B ( C x. i ) ) = 1
              )
            )
          )
      )
    )
  ) $.
$}

ntp4vc-inv-remove-definition $a |- (
  ( NTP4VCInvRemove A B C )
  <->
  (
    ( # ` A ) = ( # ` B )
    /\
    (
      -. ( NTP4VCAtBool B 2 ) = 1
      /\
      (
        ( NTP4VCAllPrimes B C )
        /\
        (
          C e. Prime
          /\
          (
            -. ( NTP4VCAtBool B C ) = 1
            /\
            ( NTP4VCInvNexts A ( # ` A ) )
          )
        )
      )
    )
  )
) $.

${
  $d i A B C $.

  ntp4vc-not-next-definition $a |- (
    ( NTP4VCNotNext A B C )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        2 <_ ( # ` A )
        /\
        (
          2 <_ C
          /\
          A. i e. ZZ
            (
              (
                2 <_ i
                /\
                i <_ ( NTP4VCTDiv ( ( # ` A ) - 1 ) C )
              )
              ->
              (
                ( NTP4VCAtInt B i ) <_
                  ( NTP4VCTDiv ( ( # ` A ) - 1 ) C )
                ->
                (
                  -. ( NTP4VCAtBool A i ) = 1
                  ->
                  -. ( NTP4VCAtBool A ( NTP4VCAtInt B i ) ) = 1
                )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-is-copy-definition $a |- (
    ( NTP4VCIsCopy A B )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < ( # ` A )
          )
          ->
          (
            -. ( NTP4VCAtBool A i ) = 1
            ->
            -. ( NTP4VCAtBool B i ) = 1
          )
        )
    )
  ) $.
$}

${
  $d i j A B C $.

  ntp4vc-all-elim-partial-definition $a |- (
    ( NTP4VCAllElimPartial A B C )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. ZZ
        (
          (
            C <_ i
            /\
            i < ( # ` A )
          )
          ->
          A. j e. ZZ
            (
              (
                i < j
                /\
                j < ( NTP4VCAtInt B i )
              )
              ->
              ( NTP4VCAtBool A j ) = 1
            )
        )
    )
  ) $.
$}

${
  $d i A B C D $.

ntp4vc-not-next-partial-definition $a |- (
    ( NTP4VCNotNextPartial A B C D )
    <->
    (
      ( # ` A ) = ( # ` B )
      /\
      (
        2 <_ ( # ` A )
        /\
        (
          2 <_ C
          /\
          (
            D <_ ( NTP4VCTDiv ( ( # ` A ) - 1 ) C )
            /\
            A. i e. ZZ
              (
                (
                  2 <_ i
                  /\
                  i < D
                )
                ->
                (
                  ( NTP4VCAtInt B i ) <_
                    ( NTP4VCTDiv ( ( # ` A ) - 1 ) C )
                  ->
                  (
                    -. ( NTP4VCAtBool A i ) = 1
                    ->
                    -. ( NTP4VCAtBool A ( NTP4VCAtInt B i ) ) = 1
                  )
                )
              )
          )
        )
      )
  )
) $.

ntp4vc-loop-inv-definition $a |- (
  ( NTP4VCLoopInv A B C D E F G )
  <->
  (
    (
      (
        D <_ E
        /\
        E <_ G
      )
      /\
      (
        (
          3 <_ D
          /\
          D <_ G
        )
        /\
        (
          ( E mod 2 ) = 1
          /\
          (
            (
              E <_ F
              /\
              F < ( NTP4VCAtInt A E )
            )
            /\
            (
              ( NTP4VCAtInt A F ) = ( NTP4VCAtInt A E )
              /\
              ( NTP4VCAtBool B ( D x. D ) ) = 1
            )
          )
        )
      )
    )
    /\
    (
      ( NTP4VCInvRemove A B D )
      /\
      (
        ( NTP4VCPreviously B D )
        /\
        (
          -. ( NTP4VCAtBool B E ) = 1
          /\
          (
            ( NTP4VCIsCopy B C )
            /\
            (
              ( NTP4VCAllElimPartial C A F )
              /\
              (
                ( NTP4VCNotNext C A D )
                /\
                (
                  (
                    NTP4VCPrimeMarked
                      C B D ( NTP4VCAtInt A F )
                  )
                  /\
                  (
                    ( NTP4VCNotNextPartial B A D E )
                    /\
                    ( NTP4VCOnly B ( D + 1 ) )
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

ntp4vc-exit-definition $a |- (
  ( NTP4VCExit A B C D )
  <->
  (
    ( NTP4VCInvRemove A B D )
    /\
    (
      ( NTP4VCNotNext B A ( NTP4VCAtInt A D ) )
      /\
      (
        ( NTP4VCIsCopy B C )
        /\
        (
          ( NTP4VCPreviously B D )
          /\
          (
            ( NTP4VCPrimeMarked C B D ( # ` B ) )
            /\
            ( NTP4VCOnly B ( D + 1 ) )
          )
        )
      )
    )
  )
) $.

ntp4vc-final-post-definition $a |- (
  ( NTP4VCFinalPost A B C )
  <->
  (
    ( NTP4VCInvRemove A B C )
    /\
    (
      ( NTP4VCNotNext B A ( NTP4VCAtInt A C ) )
      /\
      (
        ( NTP4VCPreviously B ( NTP4VCAtInt A C ) )
        /\
        ( NTP4VCOnly B ( NTP4VCAtInt A C ) )
      )
    )
  )
) $.

${
  $d t A B C D E F G $.

  ntp4vc-finalize-definition $a |- (
    ( NTP4VCFinalize A B C D E F G )
    <->
    A. t e. A
      (
        ( D ` t ) = ( D ` E )
        ->
        (
          ( NTP4VCExit ( B ` t ) ( C ` t ) F G )
          ->
          ( NTP4VCFinalPost ( B ` t ) ( C ` t ) G )
        )
      )
  ) $.
$}

ntp4vc-unmarked-step-definition $a |- (
  ( NTP4VCUnmarkedStep A B C D E F G H )
  <->
  (
    (
      0 <_ ( H - ( NTP4VCAtInt A F ) )
      /\
      (
        H - ( NTP4VCAtInt B G )
      ) < (
        H - ( NTP4VCAtInt A F )
      )
    )
    /\
    ( NTP4VCLoopInv B C D E G G H )
  )
) $.

${
  $d t A B C D E F G H I J K L $.

  ntp4vc-marked-advance-definition $a |- (
    (
      NTP4VCMarkedAdvance A B C D E F G H I J K L
    )
    <->
    A. t e. A
      (
        (
          ( C ` t ) = ( C ` F )
          /\
          ( D ` t ) = ( D ` F )
        )
        ->
        (
          ( B ` t ) =
            ( NTP4VCSet ( B ` F ) I K )
          ->
          (
            (
              0 <_ ( L - ( NTP4VCAtInt ( B ` E ) I ) )
              /\
              (
                L - ( NTP4VCAtInt ( B ` t ) I )
              ) < (
                L - ( NTP4VCAtInt ( B ` E ) I )
              )
            )
            /\
            (
              NTP4VCLoopInv
                ( B ` t ) ( C ` t ) G H I J L
            )
          )
        )
      )
  ) $.
$}

${
  $d j o A B C D E F G H I J K $.

  ntp4vc-marked-case-definition $a |- (
    ( NTP4VCMarkedCase A B C D E F G H I J K )
    <->
    (
      (
        (
          3 <_ J
          /\
          J <_ ( D ` F )
        )
        /\
        ( J mod 2 ) = 1
      )
      /\
      A. o e. NTP4VCBV63
        (
          (
            (
              3 <_ o
              /\
              o <_ ( ( D ` F ) + 1 )
            )
            /\
            (
              o = ( NTP4VCAtInt ( B ` F ) J )
              /\
              (
                ( o mod 2 ) = 1
                \/
                o = ( ( D ` F ) + 1 )
              )
            )
          )
          ->
          (
            (
              (
                (
                  0 <_ I
                  /\
                  I <_ ( D ` F )
                )
                /\
                (
                  I < o
                  /\
                  o <_ ( ( D ` F ) + 1 )
                )
              )
              /\
              (
                ( I mod 2 ) = 1
                /\
                (
                  A. j e. ZZ
                    (
                      (
                        I < j
                        /\
                        j < o
                      )
                      ->
                      ( NTP4VCAtBool ( C ` F ) j ) = 1
                    )
                  /\
                  (
                    -. ( NTP4VCAtBool ( C ` F ) I ) = 1
                    /\
                    (
                      ( o mod 2 ) = 1
                      \/
                      o = ( ( D ` F ) + 1 )
                    )
                  )
                )
              )
            )
            /\
            (
              NTP4VCMarkedAdvance
                A B C D E F G H I J o K
            )
          )
        )
    )
  ) $.
$}

${
  $d t A B C D E F G H I J K $.

  ntp4vc-after-mark-definition $a |- (
    ( NTP4VCAfterMark A B C D E F G H I J K )
    <->
    (
      ( NTP4VCIn63 ( G x. I ) )
      /\
      A. o e. NTP4VCBV63
        (
          o = ( G x. I )
          ->
          (
            (
              (
                0 <_ o
                /\
                o <_ ( D ` E )
              )
              /\
              ( o mod 2 ) = 1
            )
            /\
            A. t e. A
              (
                (
                  ( B ` t ) = ( B ` E )
                  /\
                  ( D ` t ) = ( D ` E )
                )
                ->
                (
                  ( C ` t ) =
                    ( NTP4VCSet ( C ` E ) o 1 )
                  ->
                  (
                    (
                      (
                        0 <_ I
                        /\
                        I <_ ( D ` t )
                      )
                      /\
                      ( I mod 2 ) = 1
                    )
                    /\
                    (
                      (
                        ( NTP4VCAtBool ( C ` t ) I ) = 1
                        ->
                        (
                          NTP4VCMarkedCase
                            A B C D E t F G H I K
                        )
                      )
                      /\
                      (
                        -. ( NTP4VCAtBool ( C ` t ) I ) = 1
                        ->
                        (
                          NTP4VCUnmarkedStep
                            ( B ` E ) ( B ` t ) ( C ` t )
                            F G H I K
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

ntp4vc-bool-step-definition $a |- (
  ( NTP4VCBoolStep A B C D E F G H I J K L )
  <->
  (
    (
      L = 1
      ->
      (
        (
          I <_ J
          ->
          (
            NTP4VCAfterMark
              A B C D E F G H I J K
          )
        )
        /\
        (
          -. I <_ J
          ->
          ( NTP4VCExit ( B ` E ) ( C ` E ) F G )
        )
      )
    )
    /\
    (
      -. L = 1
      ->
      ( NTP4VCExit ( B ` E ) ( C ` E ) F G )
    )
  )
) $.

${
  $d o A B C D E F G H I J K $.

  ntp4vc-scan-step-definition $a |- (
    ( NTP4VCScanStep A B C D E F G H I J K )
    <->
    A. o e. 2
      (
        (
          (
            0 <_ I
            ->
            (
              2 <_ ( D ` E )
              /\
              o = if (
                I <_ ( D ` E ) ,
                1 ,
                0
              )
            )
          )
          /\
          (
            -. 0 <_ I
            ->
            o = 0
          )
        )
        ->
        (
          NTP4VCBoolStep
            A B C D E F G H I J K o
        )
      )
  ) $.
$}

${
  $d n A B C D E F G H I J $.

  ntp4vc-next-step-definition $a |- (
    ( NTP4VCNextStep A B C D E F G H I J )
    <->
    A. n e. NTP4VCBV63
      (
        (
          (
            3 <_ n
            /\
            n <_ ( ( D ` E ) + 1 )
          )
          /\
          (
            n = ( NTP4VCAtInt ( B ` E ) H )
            /\
            (
              ( n mod 2 ) = 1
              \/
              n = ( ( D ` E ) + 1 )
            )
          )
        )
        ->
        (
          NTP4VCScanStep
            A B C D E F G H n I J
        )
      )
  ) $.
$}

ntp4vc-loop-body-definition $a |- (
  ( NTP4VCLoopBody A B C D E F G H I J K )
  <->
  (
    (
      (
        3 <_ H
        /\
        H <_ ( D ` E )
      )
      /\
      ( H mod 2 ) = 1
    )
    /\
    (
      NTP4VCNextStep
        A B C D E F G H J K
    )
  )
) $.

${
  $d p t x A B C D E F G H I $.

  ntp4vc-main-loop-definition $a |- (
    ( NTP4VCMainLoop A B C D E F G H I )
    <->
    A. t e. A
      (
        ( D ` t ) = ( D ` E )
        ->
        A. p e. NTP4VCBV63 A. x e. ZZ
          (
            (
              NTP4VCLoopInv
                ( B ` t ) ( C ` t ) I F p x H
            )
            ->
            (
              NTP4VCLoopBody
                A B C D t I F p x G H
            )
          )
      )
  ) $.
$}

${
  $d o t A B C D E F G H $.

  ntp4vc-square-step-definition $a |- (
    ( NTP4VCSquareStep A B C D E F G H )
    <->
    (
      ( NTP4VCIn63 ( F x. F ) )
      /\
      A. o e. NTP4VCBV63
        (
          o = ( F x. F )
          ->
          (
            (
              (
                0 <_ o
                /\
                o <_ ( D ` E )
              )
              /\
              ( o mod 2 ) = 1
            )
            /\
            A. t e. A
              (
                (
                  ( B ` t ) = ( B ` E )
                  /\
                  ( D ` t ) = ( D ` E )
                )
                ->
                (
                  ( C ` t ) =
                    ( NTP4VCSet ( C ` E ) o 1 )
                  ->
                  (
                    (
                      NTP4VCLoopInv
                        ( B ` t ) ( C ` t ) H F F F G
                    )
                    /\
                    (
                      NTP4VCFinalize
                        A B C D t H F
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
  $d d t A B C D E F $.

  $( Source carrier, accessors, invariant, theorem parameters, and facts. $)

  ntp4vc-state-carrier-nonempty $e |- A =/= (/) $.
  ntp4vc-nexts-function $e |- B e. ( ( Word ZZ ) ^m A ) $.
  ntp4vc-marked-function $e |- C e. ( ( Word 2 ) ^m A ) $.
  ntp4vc-max-function $e |- D e. ( NTP4VCBV63 ^m A ) $.

  ntp4vc-state-invariant $e |- A. t e. A
    ( NTP4VCStateInv ( B ` t ) ( C ` t ) ( D ` t ) ) $.

  ntp4vc-n-word $e |- E e. NTP4VCBV63 $.
  ntp4vc-t1-state $e |- F e. A $.
  ntp4vc-fact0 $e |- 3 <_ E $.
  ntp4vc-fact1 $e |- E <_ ( D ` F ) $.
  ntp4vc-fact2 $e |- ( E x. E ) <_ ( D ` F ) $.
  ntp4vc-fact3 $e |- ( NTP4VCInvRemove ( B ` F ) ( C ` F ) E ) $.
  ntp4vc-fact4 $e |- ( NTP4VCPreviously ( C ` F ) E ) $.
  ntp4vc-fact5 $e |- ( NTP4VCOnly ( C ` F ) E ) $.
  ntp4vc-fact6 $e |- ( NTP4VCNotNext ( C ` F ) ( B ` F ) E ) $.

  ntp4vc-pearl-euler-sieve-remove-products-vc $a |- (
    2 <_ ( D ` F )
    ->
    (
      (
        E =/= 0
        /\
        ( NTP4VCIn63 ( NTP4VCTDiv ( D ` F ) E ) )
      )
      /\
      A. d e. NTP4VCBV63
        (
          d = ( NTP4VCTDiv ( D ` F ) E )
          ->
          (
            (
              NTP4VCMainLoop
                A B C D F E d ( D ` F ) ( C ` F )
            )
            /\
            (
              NTP4VCSquareStep
                A B C D F E ( D ` F ) ( C ` F )
            )
          )
        )
    )
  ) $.
$}
$}
