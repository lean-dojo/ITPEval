$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieveImpl_createqtvc: the Euler-sieve constructor
  verification condition initializes the linked-list, marking, and compressed
  array representations and establishes the complete sieve-state invariant
  and constructor postconditions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCBV63 is the exact signed-63-bit integer interval. Integer and Boolean
  lists are arbitrary SetMM words over ZZ and 2. NTP4VCAtInt and
  NTP4VCAtBool reproduce totalized source lookup, and NTP4VCSet reproduces
  source list update after integer-to-natural coercion.

  NTP4VCTDiv2 is signed division by two truncated toward zero. In particular,
  the array length follows the pinned Why3 expression (max - 1) / 2 + 1;
  it is not a remainder. NTP4VCEdiv2 is Why3 Euclidean division by positive
  two in the nonnegative invariant and postcondition occurrences.

  The remaining named predicates are definitional factors of the generated
  verification condition. Expanding them recovers every source carrier,
  accessor, quantifier, implication, allocation specification, array-update
  relation, state invariant, and constructor postcondition. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCIn63 NTP4VCBV63 NTP4VCToNat
  NTP4VCAtInt NTP4VCAtBool NTP4VCSet
  NTP4VCTDiv2 NTP4VCEdiv2 NTP4VCAbs
  NTP4VCInvNexts NTP4VCAllEliminated
  NTP4VCArrayInv NTP4VCParityInv NTP4VCArrayState
  NTP4VCJumpInv NTP4VCStateInv
  NTP4VCFc NTP4VCMarkBit NTP4VCInitEntry
  NTP4VCNextsInit NTP4VCMarkedInit
  NTP4VCPrefix NTP4VCArrayMake NTP4VCCreatePost
  NTP4VCFinal NTP4VCStep NTP4VCFor NTP4VCArrayBody
$.

ntp4vc-in63-syntax $a wff ( NTP4VCIn63 A ) $.
ntp4vc-bv63-syntax $a class NTP4VCBV63 $.
ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-int-syntax $a class ( NTP4VCAtInt A B ) $.
ntp4vc-at-bool-syntax $a class ( NTP4VCAtBool A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-ediv2-syntax $a class ( NTP4VCEdiv2 A ) $.
ntp4vc-abs-syntax $a class ( NTP4VCAbs A ) $.
ntp4vc-inv-nexts-syntax $a wff ( NTP4VCInvNexts A B ) $.
ntp4vc-all-eliminated-syntax
  $a wff ( NTP4VCAllEliminated A B ) $.
ntp4vc-array-inv-syntax $a wff ( NTP4VCArrayInv A B ) $.
ntp4vc-parity-inv-syntax
  $a wff ( NTP4VCParityInv A B C ) $.
ntp4vc-array-state-syntax
  $a wff ( NTP4VCArrayState A B C D E ) $.
ntp4vc-jump-inv-syntax $a wff ( NTP4VCJumpInv A B C ) $.
ntp4vc-state-inv-syntax
  $a wff ( NTP4VCStateInv A B C D E ) $.
ntp4vc-fc-syntax $a class ( NTP4VCFc A B ) $.
ntp4vc-mark-bit-syntax $a class ( NTP4VCMarkBit A ) $.
ntp4vc-init-entry-syntax
  $a class ( NTP4VCInitEntry A B C ) $.
ntp4vc-nexts-init-syntax $a class ( NTP4VCNextsInit A ) $.
ntp4vc-marked-init-syntax $a class ( NTP4VCMarkedInit A ) $.
ntp4vc-prefix-syntax $a wff ( NTP4VCPrefix A B C D ) $.
ntp4vc-array-make-syntax $a wff ( NTP4VCArrayMake A B ) $.
ntp4vc-create-post-syntax
  $a wff ( NTP4VCCreatePost A B C D E ) $.
ntp4vc-final-syntax
  $a wff ( NTP4VCFinal A B C D E F G H I J K L ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F G H I J K L M N ) $.
ntp4vc-for-syntax
  $a wff ( NTP4VCFor A B C D E F G H I J K L ) $.
ntp4vc-array-body-syntax
  $a wff ( NTP4VCArrayBody A B C D E F G H I J K ) $.

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
) = if ( 0 <_ A , A , 0 ) $.

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
      if ( k = ( NTP4VCToNat B ) , C , ( A ` k ) )
  ) $.
$}

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-ediv2-definition $a |- (
  NTP4VCEdiv2 A
) = ( |_ ` ( A / 2 ) ) $.

ntp4vc-abs-definition $a |- (
  NTP4VCAbs A
) = if ( A < 0 , ( -u A ) , A ) $.

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
  $d i A B $.
  ntp4vc-array-inv-definition $a |- (
    ( NTP4VCArrayInv A B )
    <->
    (
      0 <_ B
      /\
      (
        B = ( # ` A )
        /\
        (
          ( # ` A ) < ( 2 ^ ; 6 2 )
          /\
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i < ( # ` A )
              )
              ->
              ( NTP4VCIn63 ( NTP4VCAtInt A i ) )
            )
        )
      )
    )
  ) $.
$}

${
  $d i A B C $.
  ntp4vc-parity-inv-definition $a |- (
    ( NTP4VCParityInv A B C )
    <->
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
            ( NTP4VCAtBool A i ) = 1
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
                ( ( NTP4VCAtInt B i ) mod 2 ) = 1
                \/
                ( NTP4VCAtInt B i ) = ( C + 1 )
              )
            )
          )
        /\
        (
          ( NTP4VCAtInt B C ) = ( C + 1 )
          /\
          (
            (
              ( ( C - 1 ) mod 2 ) = 0
              ->
              ( NTP4VCAtInt B ( C - 1 ) ) = C
            )
            /\
            (
              ( ( C - 1 ) mod 2 ) = 1
              ->
              ( NTP4VCAtInt B ( C - 1 ) ) = ( C + 1 )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d i A B C D E $.
  ntp4vc-array-state-definition $a |- (
    ( NTP4VCArrayState A B C D E )
    <->
    (
      ( # ` A ) = ( E + 1 )
      /\
      (
        A. i e. ZZ
          (
            (
              0 <_ i
              /\
              i <_ E
            )
            ->
            (
              ( -u ( D + 1 ) ) <_ ( NTP4VCAtInt A i )
              /\
              ( NTP4VCAtInt A i ) <_ ( D + 1 )
            )
          )
        /\
        (
          A. i e. ZZ
            (
              (
                0 <_ i
                /\
                i <_ E
              )
              ->
              (
                ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                <->
                ( NTP4VCAtInt A i ) < 0
              )
            )
          /\
          (
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i <_ E
                )
                ->
                (
                  -. ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                  ->
                  ( NTP4VCAtInt A i ) =
                    ( NTP4VCAtInt B ( ( 2 x. i ) + 1 ) )
                )
              )
            /\
            A. i e. ZZ
              (
                (
                  0 <_ i
                  /\
                  i <_ E
                )
                ->
                (
                  ( NTP4VCAtBool C ( ( 2 x. i ) + 1 ) ) = 1
                  ->
                  ( NTP4VCAtInt A i ) =
                    ( -u ( NTP4VCAtInt B ( ( 2 x. i ) + 1 ) ) )
                )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d i j A B C $.
  ntp4vc-jump-inv-definition $a |- (
    ( NTP4VCJumpInv A B C )
    <->
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i <_ C
          )
          ->
          (
            (
              i < ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
              /\
              ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
                <_ ( C + 1 )
            )
            /\
            ( NTP4VCAbs ( NTP4VCAtInt A i ) ) <_ ( B + 1 )
          )
        )
      /\
      A. i e. ZZ A. j e. ZZ
        (
          (
            0 <_ i
            /\
            i <_ C
          )
          ->
          (
            (
              i < j
              /\
              j < ( NTP4VCEdiv2 ( NTP4VCAbs ( NTP4VCAtInt A i ) ) )
            )
            ->
            ( NTP4VCAtInt A j ) < 0
          )
        )
    )
  ) $.
$}

ntp4vc-state-inv-definition $a |- (
  ( NTP4VCStateInv A B C D E )
  <->
  (
    D < ( ( 2 ^ ; 6 2 ) - 1 )
    /\
    (
      3 <_ D
      /\
      (
        ( # ` A ) = ( # ` B )
        /\
        (
          ( # ` B ) = ( D + 1 )
          /\
          (
            ( NTP4VCEdiv2 ( D - 1 ) ) = E
            /\
            (
              ( NTP4VCInvNexts A ( # ` A ) )
              /\
              (
                ( NTP4VCAllEliminated B A )
                /\
                (
                  ( NTP4VCParityInv B A D )
                  /\
                  (
                    ( NTP4VCArrayState C A B D E )
                    /\
                    ( NTP4VCJumpInv C D E )
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

ntp4vc-fc-definition $a |- (
  NTP4VCFc A B
) = if (
  B = A ,
  ( A + 1 ) ,
  if (
    B = ( A - 1 ) ,
    if ( ( B mod 2 ) = 0 , A , ( A + 1 ) ) ,
    if (
      ( B < 3 \/ ( B mod 2 ) = 0 ) ,
      ( B + 1 ) ,
      ( B + 2 )
    )
  )
) $.

ntp4vc-mark-bit-definition $a |- (
  NTP4VCMarkBit A
) = if (
  ( A = 0 \/ ( A = 1 \/ ( 2 < A /\ ( A mod 2 ) = 0 ) ) ) ,
  1 ,
  0
) $.

ntp4vc-init-entry-definition $a |- (
  NTP4VCInitEntry A B C
) = if (
  C = ( B - 1 ) ,
  ( A + 1 ) ,
  if ( C = 0 , ( -u 2 ) , ( ( 2 x. C ) + 3 ) )
) $.

${
  $d k A $.
  ntp4vc-nexts-init-definition $a |- (
    NTP4VCNextsInit A
  ) = (
    k e. ( 0 ..^ ( A + 1 ) ) |-> ( NTP4VCFc A k )
  ) $.
$}

${
  $d k A $.
  ntp4vc-marked-init-definition $a |- (
    NTP4VCMarkedInit A
  ) = (
    k e. ( 0 ..^ ( A + 1 ) ) |-> ( NTP4VCMarkBit k )
  ) $.
$}

${
  $d j A B C D $.
  ntp4vc-prefix-definition $a |- (
    ( NTP4VCPrefix A B C D )
    <->
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < D
        )
        ->
        ( NTP4VCAtInt A j ) = ( NTP4VCInitEntry B C j )
      )
  ) $.
$}

${
  $d i A B $.
  ntp4vc-array-make-definition $a |- (
    ( NTP4VCArrayMake A B )
    <->
    (
      A. i e. ZZ
        (
          (
            0 <_ i
            /\
            i < B
          )
          ->
          ( NTP4VCAtInt A i ) = ( -u 2 )
        )
      /\
      ( # ` A ) = B
    )
  ) $.
$}

${
  $d i z A B C D E $.
  ntp4vc-create-post-definition $a |- (
    ( NTP4VCCreatePost A B C D E )
    <->
    (
      ( C ` D ) = E
      /\
      (
        (
          (
            ( NTP4VCAtBool ( B ` D ) 0 )
              = ( NTP4VCAtBool ( B ` D ) 1 )
            /\
            ( NTP4VCAtBool ( B ` D ) 1 ) = 1
          )
          /\
          -. ( NTP4VCAtBool ( B ` D ) 2 ) = 1
        )
        /\
        (
          A. i e. ZZ
            (
              (
                1 <_ i
                /\
                i <_ ( NTP4VCEdiv2 ( E - 1 ) )
              )
              ->
              -. ( NTP4VCAtBool ( B ` D ) ( ( 2 x. i ) + 1 ) ) = 1
            )
          /\
          (
            A. i e. ZZ
              (
                (
                  2 <_ i
                  /\
                  i <_ ( NTP4VCEdiv2 ( E + 1 ) )
                )
                ->
                (
                  ( 2 x. i ) <_ E
                  ->
                  ( NTP4VCAtBool ( B ` D ) ( 2 x. i ) ) = 1
                )
              )
            /\
            (
              A. i e. ZZ
                (
                  (
                    1 <_ i
                    /\
                    i <_ ( NTP4VCEdiv2 ( E - 1 ) )
                  )
                  ->
                  (
                    ( ( 2 x. i ) + 1 ) < ( E - 1 )
                    ->
                    ( NTP4VCAtInt ( A ` D ) ( ( 2 x. i ) + 1 ) )
                      = ( ( 2 x. i ) + 3 )
                  )
                )
              /\
              (
                A. i e. ZZ
                  (
                    (
                      2 <_ i
                      /\
                      i <_ ( NTP4VCEdiv2 ( E - 1 ) )
                    )
                    ->
                    (
                      ( 2 x. i ) < ( E - 1 )
                      ->
                      ( NTP4VCAtInt ( A ` D ) ( 2 x. i ) )
                        = ( ( 2 x. i ) + 1 )
                    )
                  )
                /\
                A. i e. ZZ
                  (
                    (
                      0 <_ i
                      /\
                      i <_ E
                    )
                    ->
                    (
                      ( NTP4VCAtBool ( B ` D ) i ) = 1
                      ->
                      (
                        i < 2
                        \/
                        E. z e. ZZ i = ( 2 x. z )
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
  $d r A B C D E F G H I J K L $.
  ntp4vc-final-definition $a |- (
    ( NTP4VCFinal A B C D E F G H I J K L )
    <->
    (
      ( NTP4VCStateInv J K ( B ` L ) H I )
      /\
      A. r e. A
        (
          (
            ( C ` r ) = J
            /\
            (
              ( D ` r ) = K
              /\
              (
                ( E ` r ) = L
                /\
                (
                  ( F ` r ) = H
                  /\
                  ( G ` r ) = I
                )
              )
            )
          )
          ->
          ( NTP4VCCreatePost C D F r H )
        )
    )
  ) $.
$}

${
  $d a o p q A B C D E F G H I J K L M N $.
  ntp4vc-step-definition $a |- (
    ( NTP4VCStep A B C D E F G H I J K L M N )
    <->
    (
      (
        (
          1 <_ N
          /\
          N <_ L
        )
        /\
        ( NTP4VCPrefix ( C ` M ) J K N )
      )
      ->
      (
        ( NTP4VCIn63 ( K - 1 ) )
        /\
        A. o e. NTP4VCBV63
          (
            o = ( K - 1 )
            ->
            (
              ( N = o -> N = o )
              ->
              (
                (
                  (
                    N = o
                    ->
                    ( NTP4VCIn63 ( J + 1 ) )
                  )
                  /\
                  (
                    -. N = o
                    ->
                    (
                      ( NTP4VCIn63 ( 2 x. N ) )
                      /\
                      A. q e. NTP4VCBV63
                        (
                          q = ( 2 x. N )
                          ->
                          ( NTP4VCIn63 ( q + 3 ) )
                        )
                    )
                  )
                )
                /\
                A. q e. NTP4VCBV63
                  (
                    (
                      (
                        N = o
                        /\
                        q = ( J + 1 )
                      )
                      \/
                      (
                        -. N = o
                        /\
                        E. p e. NTP4VCBV63
                          (
                            p = ( 2 x. N )
                            /\
                            q = ( p + 3 )
                          )
                      )
                    )
                    ->
                    (
                      (
                        0 <_ N
                        /\
                        N < ( # ` ( C ` M ) )
                      )
                      /\
                      A. a e. A
                        (
                          ( D ` a ) = ( D ` M )
                          ->
                          (
                            ( C ` a ) = ( NTP4VCSet ( C ` M ) N q )
                            ->
                            ( NTP4VCPrefix ( C ` a ) J K ( N + 1 ) )
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
  $d a i o A B C D E F G H I J K L $.
  ntp4vc-for-definition $a |- (
    ( NTP4VCFor A B C D E F G H I J K L )
    <->
    (
      ( NTP4VCIn63 ( K - 1 ) )
      /\
      A. o e. NTP4VCBV63
        (
          o = ( K - 1 )
          ->
          (
            (
              1 <_ ( o + 1 )
              ->
              (
                ( NTP4VCPrefix ( C ` L ) J K 1 )
                /\
                A. a e. A
                  (
                    ( D ` a ) = ( D ` L )
                    ->
                    (
                      A. i e. NTP4VCBV63
                        (
                          NTP4VCStep
                            A B C D E F G H I J K o a i
                        )
                      /\
                      (
                        ( NTP4VCPrefix ( C ` a ) J K ( o + 1 ) )
                        ->
                        (
                          NTP4VCFinal
                            B C E F G H I J o
                            ( NTP4VCNextsInit J )
                            ( NTP4VCMarkedInit J )
                            a
                        )
                      )
                    )
                  )
              )
            )
            /\
            (
              ( o + 1 ) < 1
              ->
              (
                NTP4VCFinal
                  B C E F G H I J o
                  ( NTP4VCNextsInit J )
                  ( NTP4VCMarkedInit J )
                  L
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d a A B C D E F G H I J K $.
  ntp4vc-array-body-definition $a |- (
    ( NTP4VCArrayBody A B C D E F G H I J K )
    <->
    (
      0 <_ K
      /\
      A. a e. A
        (
          ( NTP4VCArrayMake ( C ` a ) K )
          ->
          (
            NTP4VCFor
              A B C D E F G H I J K a
          )
        )
    )
  ) $.
$}

${
  $d a b i o p q r t x A B C D E F G H I J K $.

  $( Source abstract carriers. $)
  ntp4vc-array-carrier-nonempty $e |- A =/= (/) $.
  ntp4vc-state-carrier-nonempty $e |- B =/= (/) $.

  $( Source accessors and their exact full domains/codomains. $)
  ntp4vc-elts-function $e |- C e. ( ( Word ZZ ) ^m A ) $.
  ntp4vc-size-function $e |- D e. ( ZZ ^m A ) $.
  ntp4vc-nexts-function $e |- E e. ( ( Word ZZ ) ^m B ) $.
  ntp4vc-marked-function $e |- F e. ( ( Word 2 ) ^m B ) $.
  ntp4vc-arr-function $e |- G e. ( A ^m B ) $.
  ntp4vc-max-function $e |- H e. ( NTP4VCBV63 ^m B ) $.
  ntp4vc-max-arr-function $e |- I e. ( NTP4VCBV63 ^m B ) $.

  $( Universal imported array and state invariants. $)
  ntp4vc-array-invariant $e |- A. a e. A
    ( NTP4VCArrayInv ( C ` a ) ( D ` a ) ) $.

  ntp4vc-state-invariant $e |- A. t e. B
    (
      NTP4VCStateInv
        ( E ` t ) ( F ` t ) ( C ` ( G ` t ) ) ( H ` t ) ( I ` t )
    ) $.

  ntp4vc-state-injective $e |- A. a e. B A. b e. B
    (
      (
        ( E ` a ) = ( E ` b )
        /\
        (
          ( F ` a ) = ( F ` b )
          /\
          (
            ( G ` a ) = ( G ` b )
            /\
            (
              ( H ` a ) = ( H ` b )
              /\
              ( I ` a ) = ( I ` b )
            )
          )
        )
      )
      ->
      a = b
    ) $.

  $( Source theorem parameter max and its two preconditions. $)
  ntp4vc-max-parameter $e |- J e. NTP4VCBV63 $.
  ntp4vc-max-below-machine-max $e |- J < ( ( 2 ^ ; 6 2 ) - 1 ) $.
  ntp4vc-max-at-least-three $e |- 3 <_ J $.

  ntp4vc-pearl-euler-sieve-create-vc $a |- (
    ( NTP4VCIn63 ( J - 1 ) )
    /\
    A. o e. NTP4VCBV63
      (
        o = ( J - 1 )
        ->
        (
          (
            2 =/= 0
            /\
            ( NTP4VCIn63 ( NTP4VCTDiv2 o ) )
          )
          /\
          A. p e. NTP4VCBV63
            (
              p = ( NTP4VCTDiv2 o )
              ->
              (
                ( NTP4VCIn63 ( p + 1 ) )
                /\
                A. q e. NTP4VCBV63
                  (
                    q = ( p + 1 )
                    ->
                    (
                      0 <_ ( J + 1 )
                      /\
                      (
                        (
                          ( # ` ( NTP4VCNextsInit J ) ) = ( J + 1 )
                          /\
                          A. i e. ZZ
                            (
                              (
                                0 <_ i
                                /\
                                i < ( J + 1 )
                              )
                              ->
                              ( NTP4VCAtInt ( NTP4VCNextsInit J ) i )
                                = ( NTP4VCFc J i )
                            )
                        )
                        ->
                        (
                          A. i e. ZZ
                            (
                              -. i = 0
                              ->
                              (
                                -. i = 1
                                ->
                                (
                                  2 < i
                                  ->
                                  2 =/= 0
                                )
                              )
                            )
                          /\
                          (
                            0 <_ ( J + 1 )
                            /\
                            (
                              (
                                ( # ` ( NTP4VCMarkedInit J ) ) = ( J + 1 )
                                /\
                                A. i e. ZZ
                                  (
                                    (
                                      0 <_ i
                                      /\
                                      i < ( J + 1 )
                                    )
                                    ->
                                    ( NTP4VCAtBool ( NTP4VCMarkedInit J ) i )
                                      = ( NTP4VCMarkBit i )
                                  )
                              )
                              ->
                              (
                                NTP4VCArrayBody
                                  A B C D E F G H I J q
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
